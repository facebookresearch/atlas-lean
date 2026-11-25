# A planar harmonic function is constant near an interior maximum

Let $U \subseteq \mathbb{C}$ be open and let $u : \mathbb{C} \to \mathbb{R}$ be harmonic on $U$. If $u$
attains its maximum over $U$ at $z \in U$, then $u$ is constant on some disc around $z$ contained
in $U$.

**Proof idea.** On a disc $B \subseteq U$ around $z$, $u = \operatorname{Re} F$ with
$F$ holomorphic. Then $|e^{F}| = e^{u}$ attains its maximum over $B$ at the centre, so $e^{F}$ is
constant by the maximum modulus principle, and so is $u = \log |e^F|$. Schmidt proves the same
local step in $\mathbb{R}^n$ from the mean-value property.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), proof of Strong Maximum Principle 3.10.
