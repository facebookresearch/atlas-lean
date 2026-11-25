# Lookup in the suffix tree returns starting indices

Let $s$ be a list over $\alpha$, let
$k$ be a list over $\alpha$ extended by a fresh terminator symbol, and let $i$ be a natural number.
If looking up $k$ in the suffix tree of $s$ returns $i$, then $i \le |s|$ and $k$ is the
terminated string of $s$ with its first $i$ symbols removed.
