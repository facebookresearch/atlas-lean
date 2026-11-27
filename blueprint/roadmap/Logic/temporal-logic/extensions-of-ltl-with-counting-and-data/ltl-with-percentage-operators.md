# LTL with percentage operators

Percentage operators extend the finally-only fragment of linear temporal logic over finite words with past counting: "at least half of the earlier positions satisfy φ" (majority in the past), "exactly half of them do", or "letter σ has been among the most frequent so far".

**Base logic.** Over a finite set $\mathrm{AP}$ of atomic propositions, $\mathrm{LTL}_{\mathbf{F}}$ formulas are given by $\varphi ::= a \mid \neg\varphi \mid \varphi \wedge \varphi \mid \mathbf{F}\varphi$ with $a \in \mathrm{AP}$. They are evaluated at positions $i$ of nonempty finite words $w = w_0 w_1 \cdots w_{|w|-1}$ over $2^{\mathrm{AP}}$: $w, i \models a$ iff $a \in w_i$, Boolean connectives as usual, and $w, i \models \mathbf{F}\varphi$ iff $w, j \models \varphi$ for some $j$ with $i \leq j < |w|$. A word satisfies $\varphi$ if $w, 0 \models \varphi$; $\mathbf{G}\varphi = \neg\mathbf{F}\neg\varphi$.

**Percentage operators.** For a position $i$ let $\#_\varphi(i) = |\{j < i : w, j \models \varphi\}|$; the operators are defined by

$$
w,i \models \mathbf{M}\varphi \iff \#_\varphi(i) \geq \tfrac{i}{2}, \qquad w,i \models \mathbf{H}\varphi \iff \#_\varphi(i) = \tfrac{i}{2}, \qquad w,i \models \mathbf{MF}\,\sigma \iff \forall \tau \in \mathrm{AP}:\ \#_\sigma(i) \geq \#_\tau(i),
$$

for formulas $\varphi$ and letters $\sigma \in \mathrm{AP}$: majority in the past, exactly half in the past, and most frequent letter in the past. At $i = 0$ the counts are $0$, so $\mathbf{M}\varphi$ and $\mathbf{H}\varphi$ are true there; $\mathbf{H}\varphi$ is true only at even positions and equals $\mathbf{M}\varphi \wedge \mathbf{M}\neg\varphi$. $\mathrm{LTL}_{\mathbf{F}}[\mathbf{M}]$, $\mathrm{LTL}_{\mathbf{F}}[\mathbf{H}]$ and $\mathrm{LTL}_{\mathbf{F}}[\mathbf{MF}]$ add the respective operator.

**Problems.** A Kripke structure has finite sets of states and initial states, a total transition relation and a labelling of states by subsets of $\mathrm{AP}$; its traces are the finite words labelling finite paths from initial states. *Satisfiability* asks whether a formula has a finite model word; *model checking* asks whether some trace of a given Kripke structure satisfies a given formula.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

The formula $\mathbf{G}(r \leftrightarrow \neg g) \wedge \mathbf{G}\,\mathbf{M}r \wedge \mathbf{G}\mathbf{F}(g \wedge \mathbf{M}g)$ holds on words in which every request $r$ is eventually matched by a grant $g$ and every grant by a request, a non-regular language. Frequency LTL of Bollig, Decker and Leucker uses more expressive operators with until; its claimed undecidability proof was found to be flawed.

## Sources

- Bartosz Bednarczyk and Jakub Michaliszyn, "“Most of” leads to undecidability: Failure of adding frequencies to LTL", in *Foundations of Software Science and Computation Structures (FoSSaCS 2021)*, Lecture Notes in Computer Science 12650, Springer, 2021, pp. 82–101, doi:10.1007/978-3-030-71995-1_5; read as arXiv:2007.01233v4, <https://arxiv.org/abs/2007.01233v4>: Section 2 (words, $\mathrm{LTL}_{\mathbf{F}}$, the percentage operators and the computational problems) and Section 1.1 (related work) of arXiv:2007.01233v4.
