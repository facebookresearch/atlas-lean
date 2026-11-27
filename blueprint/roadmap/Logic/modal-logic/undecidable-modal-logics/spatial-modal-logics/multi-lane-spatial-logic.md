# Multi-lane spatial logic

Multi-lane spatial logic (MLSL) is a two-dimensional interval logic for reasoning about cars on a motorway: formulas are evaluated on views, rectangles of lanes times a real interval, and are combined by horizontal and vertical chop operators.

**Definition.** Fix an infinite set $\mathbb I$ of car identifiers and lanes $\mathbb L = \{0, \ldots, N\}$, $N \ge 1$. A *traffic snapshot* $TS = (\mathit{res}, \mathit{clm}, \mathit{pos}, \mathit{spd}, \mathit{acc})$ assigns to each car $C$ the sets $\mathit{res}(C), \mathit{clm}(C) \subseteq \mathbb L$ of lanes it reserves and claims, and its position, speed and acceleration in $\mathbb R$, subject to: $\mathit{res}(C) \cap \mathit{clm}(C) = \emptyset$; $1 \le |\mathit{res}(C)| \le 2$; $|\mathit{clm}(C)| \le 1$; $|\mathit{res}(C)| + |\mathit{clm}(C)| \le 2$; if $\mathit{clm}(C) \neq \emptyset$ then $\mathit{res}(C) \cup \mathit{clm}(C) = \{n, n+1\}$ for some $n$; and only finitely many cars have two reserved lanes or a claim. A *view* $V = (L, X, E)$ consists of an interval of lanes $L \subseteq \mathbb L$ (possibly empty), a real interval $X = [r, t]$ and an owner $E \in \mathbb I$. A sensor function $\Omega_E(C, TS) > 0$ gives the length of car $C$ as perceived by $E$; then $\mathit{res}_V(C) = \mathit{res}(C) \cap L$, $\mathit{clm}_V(C) = \mathit{clm}(C) \cap L$ and $\mathit{len}_V(C) = [\mathit{pos}(C), \mathit{pos}(C) + \Omega_E(C, TS)] \cap X$. $V = V_1 \ominus V_2$ splits the lanes of $V$ into a lower and an upper consecutive part, and $V = V_1 \frown V_2$ splits $X = [r, t]$ at some $s \in [r, t]$ into $[r, s]$ and $[s, t]$.

*Syntax.* Terms are $\theta ::= n \mid r \mid \mathit{ego} \mid u \mid \ell \mid \omega \mid \theta_1 + \theta_2$ over three sorts of variables $u$ (cars, reals, lanes), with $\ell$ the length $t - r$ of the view and $\omega$ its number of lanes $|L|$. Formulas of *spatial MLSL* are

$$
\varphi ::= \bot \mid \theta_1 = \theta_2 \mid \mathit{re}(c) \mid \mathit{cl}(c) \mid \varphi_1 \to \varphi_2 \mid \forall z\,\varphi \mid \varphi_1 \frown \varphi_2 \mid \tfrac{\varphi_2}{\varphi_1},
$$

with $c$ a car variable or $\mathit{ego}$ (the extension EMLSL adds modalities for the discrete and continuous transitions of snapshots, which spatial MLSL omits).

*Semantics*, for a snapshot $TS$, a view $V = (L, X, E)$ and a sort-respecting valuation $\nu$ with $\nu(\mathit{ego}) = E$: $TS, V, \nu \models \mathit{re}(c)$ iff $|L| = 1$, $t > r$, $\mathit{res}_V(\nu(c)) = L$ and $X = \mathit{len}_V(\nu(c))$, and likewise $\mathit{cl}(c)$ with $\mathit{clm}_V$; $\varphi_1 \frown \varphi_2$ holds iff $V = V_1 \frown V_2$ with $V_1 \models \varphi_1$ and $V_2 \models \varphi_2$; $\tfrac{\varphi_2}{\varphi_1}$ holds iff $V = V_1 \ominus V_2$ with $V_1 \models \varphi_1$ (lower lanes) and $V_2 \models \varphi_2$ (upper lanes); $\forall$ ranges over $\mathbb I \cup \mathbb R \cup \mathbb L$ by sort, and equality and the connectives are as usual. A formula is *satisfiable* if it holds for some snapshot, view and valuation.

## Depends on

None.

## Proof depends on

None.

## Expansion

The chop operators make MLSL a two-dimensional relative of Duration Calculus and interval temporal logic: $\frown$ chops the view horizontally along the motorway and the fraction notation chops it vertically between lanes. The empty set counts as an interval of lanes so that the smallest lane intervals have measure $0$, like point intervals of $\mathbb R$ (Definitions 2.10 to 2.12 of the source).

## Sources

- S. Linker and M. Hilscher, "Proof Theory of a Multi-Lane Spatial Logic", *Logical Methods in Computer Science* 11(3), 2015, paper 4, <https://doi.org/10.2168/LMCS-11(3:4)2015>; numbers from arXiv:1504.06986v2, <https://arxiv.org/abs/1504.06986v2>: Definitions 2.1, 2.5, 2.6, 2.10, 2.11, 2.13 to 2.15 and Remark 2.7.
