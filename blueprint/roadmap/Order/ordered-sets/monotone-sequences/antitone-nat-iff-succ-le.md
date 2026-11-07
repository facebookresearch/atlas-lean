# Successor criterion for antitone sequences

Let $\alpha$ be a preordered set. A sequence
$f : \mathbb{N} \to \alpha$ is antitone (that is, $f(n) \le f(m)$ whenever $m \le n$)
if and only if $f(n+1) \le f(n)$ for every $n \in \mathbb{N}$.

## Sources

- `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Monotone), "Convergent Sequences of the Real Numbers section", part (2): a sequence is monotone decreasing if `xₙ ≥ xₙ₊₁` for all `n`. This part was missing from the v1 formalization in `v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean`.
