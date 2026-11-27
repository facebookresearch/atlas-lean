# Merkle verifier

The verifier accepts the claim that leaf $i$ of a tree with $n$ leaves and root $r$ is $x$, with a path
$p$, when $i < n$ and recomputing from $x$ and $p$ for $\lceil \log_2 n \rceil$ levels gives $r$.
Verification takes at most $\lceil \log_2 n \rceil$ rounds, whatever the path.
