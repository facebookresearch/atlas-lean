# Counting CTL

Counting CTL extends CTL with until modalities constrained by linear conditions on how many states along the path, before the target state, satisfy given subformulas.

**Definition.** A *Kripke structure* $S = (Q, R, \ell)$ has a finite set $Q$ of states, a total transition relation $R \subseteq Q \times Q$ (every state has a successor) and a labeling $\ell : Q \to 2^{AP}$; a *run* is an infinite sequence $q_0 q_1 \cdots$ with $(q_i, q_{i+1}) \in R$. Formulas of *CCTL* are

$$
\varphi, \psi ::= P \mid \varphi \wedge \psi \mid \neg\varphi \mid \mathsf E\varphi\,\mathsf U_{[C]}\,\psi \mid \mathsf A\varphi\,\mathsf U_{[C]}\,\psi, \qquad C ::= \Big(\sum_{i=1}^m \alpha_i \cdot \sharp\varphi_i\Big) \sim k,
$$

with $P \in AP$, CCTL formulas $\varphi_i$, $\alpha_i, k \in \mathbb N$ and ${\sim} \in \{<, \le, =, \ge, >\}$; integer constants are written in binary. For a finite run prefix $\sigma = q_0 \cdots q_i$, $|\sigma|_\varphi$ is the number of positions $j \le i$ with $q_j \models \varphi$, and $\sigma \models C$ evaluates $C$ with $\sharp\varphi_i := |\sigma|_{\varphi_i}$. Then $\rho \models \varphi\,\mathsf U_{[C]}\,\psi$ iff there is $i \ge 0$ with $\rho(i) \models \psi$, $\rho(0)\cdots\rho(i-1) \models C$ and $\rho(j) \models \varphi$ for all $j < i$; $\mathsf E$ and $\mathsf A$ quantify over runs from the current state. The variants are:

- *CCTL$_1$*: every coefficient $\alpha_i$ equals $1$;
- *CCTL$_\pm$*: coefficients $\alpha_i \in \mathbb Z$ and constants $k \in \mathbb Z$, which allows *diagonal* constraints such as $\sharp\varphi - \sharp\psi \sim k$;
- *CCTL$_\wedge$*: Boolean combinations of constraints;

and their combinations, such as CCTL$_{\pm 1}$ (coefficients in $\{-1, 1\}$) and CCTL$_{\wedge\pm 1}$. The *model-checking problem* asks, given $S$, a state $q$ and a formula $\Phi$, whether $q \models \Phi$; the *satisfiability problem* asks whether some (finite) Kripke structure has a state satisfying $\Phi$.

## Depends on

- [CTL formulas](../computation-tree-logic/formula.md)

## Proof depends on

None.

## Expansion

CCTL contains CTL: $\mathsf E\varphi\,\mathsf U\,\psi$ is $\mathsf E\varphi\,\mathsf U_{[\sharp\top \ge 0]}\,\psi$. The derived modalities are $\mathsf{EF}_{[C]}\varphi = \mathsf E\top\,\mathsf U_{[C]}\,\varphi$, $\mathsf{AF}_{[C]}$, and their duals $\mathsf{AG}_{[C]}$, $\mathsf{EG}_{[C]}$. For example, $\mathsf{EF}_{[\sharp P + \sharp P' = 10]}P''$ is in CCTL$_1$. Model checking is P-complete for CCTL$_{\pm 1}$, which has diagonal constraints but no Boolean combinations inside a constraint (Theorem 4.4), and $\Delta^P_2$-complete for CCTL, CCTL$_{\wedge 1}$ and CCTL$_\wedge$ (Corollary 4.11), and satisfiability from CCTL$_1$ to CCTL$_\wedge$ is 2EXPTIME-complete (Theorem 5.2).

## Sources

- F. Laroussinie, A. Meyer and E. Petonnet, "Counting CTL", *Logical Methods in Computer Science* 9(1), 2013, paper 3, <https://doi.org/10.2168/LMCS-9(1:3)2013>; numbers from arXiv:1211.4651v4, <https://arxiv.org/abs/1211.4651v4>: Definitions 2.1 to 2.3, Theorem 4.4, Corollary 4.11 and Theorem 5.2.
