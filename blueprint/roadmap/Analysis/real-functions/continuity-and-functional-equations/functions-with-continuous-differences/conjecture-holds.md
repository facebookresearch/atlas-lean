# De Bruijn's theorem on continuous differences (Erdős Problem 907)

Let
$f : \mathbb{R} \to \mathbb{R}$ be a function such that for every $h > 0$ the function
$x \mapsto f(x + h) - f(x)$ is continuous. Then there are functions
$g, a : \mathbb{R} \to \mathbb{R}$ with $g$ continuous and $a$ additive, that is,
$a(x + y) = a(x) + a(y)$ for all real $x$ and $y$, such that $f = g + a$.

## Sources

- N. G. de Bruijn, Functions whose differences belong to a given class, Nieuw Archief voor Wiskunde (2) (1951), 194–218, https://mathscinet.ams.org/mathscinet-getitem?mr=43870; External Lean proof of Erdős Problem 907, plby/lean-proofs, https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos907.lean.
