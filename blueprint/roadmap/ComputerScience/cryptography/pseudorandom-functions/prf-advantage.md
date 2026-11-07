# PRF advantage

Let $K$, $X$, $Y$ and $S$ be finite sets with $K$, $Y$ and $S$ nonempty,
let $F : K \to X \to Y$ be a keyed function and let $D$ be a distinguisher: an oracle algorithm
with coins in $S$ that queries a function $X \to Y$ and outputs a bit. The PRF advantage of $D$
against $F$ is the real number $|p_{\mathrm{real}} - p_{\mathrm{rand}}|$, where
$p_{\mathrm{real}}$ is the probability that $D$ outputs $1$ in the real world (uniform coins
$s \in S$, oracle $F(k, \cdot)$ for a uniform key $k \in K$) and $p_{\mathrm{rand}}$ is the
probability that $D$ outputs $1$ in the random world (uniform coins, oracle a uniformly random
function $X \to Y$).
