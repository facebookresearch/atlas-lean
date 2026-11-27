# Greedy backward-selection rule

Let $g$ be a real function on the finite subsets of a set $\iota$ of features. A rule $\pi$
choosing an element $\pi(R) \in R$ of every nonempty finite set $R$ is a greedy backward-selection
rule for $g$ if it masks a feature maximizing the remaining prediction:
$g(R \setminus \{i\}) \le g(R \setminus \{\pi(R)\})$ for every nonempty $R$ and every $i \in R$.
