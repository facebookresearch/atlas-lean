# LaSalle's invariance principle

Let $\varphi = (\varphi_t)_{t \ge 0}$ be a continuous semiflow on a Hausdorff topological space $X$, let
$V : X \to \mathbb{R}$ be continuous, and let $x \in X$ have its forward orbit in a compact set $K$, with
$t \mapsto V(\varphi_t(x))$ nonincreasing. Let $E \subseteq X$ contain every $y \in K$ whose orbit keeps $V$ constant
($V(\varphi_t(y)) = V(y)$ for all $t \ge 0$), and let $M = \{y : \varphi_t(y) \in E \text{ for all } t \ge 0\}$ be the
largest forward-invariant subset of $E$. Then the ω-limit set
$\omega^+(x) = \bigcap_{s \ge 0} \overline{\{\varphi_t(x) : t \ge s\}}$ is nonempty and contained in $M$, and for every
open set $U \supseteq M$ we have $\varphi_t(x) \in U$ for all sufficiently large $t$.

## Sources

- Joseph P. LaSalle, *Some extensions of Liapunov's second method*, IRE Trans. Circuit Theory 7 (1960), no. 4,
  520–527, DOI 10.1109/tct.1960.1086720.
- Hassan K. Khalil, *Nonlinear Systems*, 3rd ed., Prentice Hall (2002), Theorem 4.4.
