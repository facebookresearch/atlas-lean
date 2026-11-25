# The off-diagonal van der Waerden numbers are not polynomially bounded

There are no
natural numbers $C$ and $A$ such that for every $k \ge 1$, every colouring of the natural numbers
in red and blue has a red $3$-term or a blue $k$-term arithmetic progression $a, a + d, \dots$
with $a \ge 1$, $d \ge 1$ and all terms in $\{1, \dots, C k^A\}$.

Equivalently, the van der Waerden number $W(3, k)$, the least $n$ such that every red/blue
colouring of $\{1, \dots, n\}$ has a red $3$-term or a blue $k$-term arithmetic progression, is
not bounded by $C k^A$ for any constants $C$ and $A$. Green proved that for some constant $c > 0$
and all sufficiently large $k$, $W(3, k) \ge k^{b(k)}$ with
$b(k) = c (\log k / \log \log k)^{1/3}$, which tends to infinity (the colours of his colouring are
swapped relative to this statement, which is symmetric).

## Sources

- AIM workshop Graph Ramsey theory, problem list, https://www.overleaf.com/read/mnvcscjjysvg, Problem 43 (same text: AimPL, Graph Ramsey Theory, section 25, http://aimpl.org/graphramsey/1/); resolution: B. Green, New lower bounds for van der Waerden numbers, Forum Math. Pi 10 (2022), e18, arXiv:2102.01543, abstract and main theorem: there is a red-blue colouring of [N] with no blue 3-term progression and no red progression of length e^{C (log N)^{3/4} (log log N)^{1/4}}, so w(3, k) ≥ k^{b(k)} with b(k) = c (log k / log log k)^{1/3} → ∞; Z. Hunter (arXiv:2111.01099) improved this to w(3, k) ≥ k^{c log k / log log k}, https://doi.org/10.1017/fmp.2022.12.
