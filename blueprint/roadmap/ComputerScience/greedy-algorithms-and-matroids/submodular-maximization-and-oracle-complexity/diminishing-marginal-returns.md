# Diminishing marginal returns characterize submodularity

For a finite set $E$ and a real-valued $f : 2^E \to \mathbb{R}$, the following are equivalent: (i) $f(A \cup B) + f(A \cap B) \le f(A) + f(B)$ for all $A, B$; (ii) for all $A \subseteq B$ and $x \notin B$, $f(B \cup \{x\}) - f(B) \le f(A \cup \{x\}) - f(A)$. Consequently, for submodular $f$ and any $A, B$, $f(B) - f(A) \le \sum_{x \in B \setminus A} \big(f(A \cup \{x\}) - f(A)\big)$ when $f$ is monotone.

## Proof sketch

(i) with $A \cup \{x\}$ and $B$ gives (ii); conversely telescope (ii) over the elements of $B \setminus A$ added to $A \cap B$ and to $A$.

## Depends on

- [Submodular set function](../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, "An Analysis of Approximations for Maximizing Submodular Set Functions I", Mathematical Programming 14, 1978.
