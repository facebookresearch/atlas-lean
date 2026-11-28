# Schummer–Vohra characterization on trees

On a finite connected tree metric graph with positive edge lengths, a deterministic facility-location mechanism with distance costs is strategyproof and onto if and only if it is the evaluation map of an extended median voter scheme. Every such mechanism is group strategyproof in the strong sense: no coalition has a joint misreport under which no member's cost increases and some member's cost strictly decreases. For $n \ge 2$ agents on a tree with at least one edge, non-dictatorial strategyproof onto mechanisms exist; for example, for three agents on a three-leaf star, the tree median, which places the facility at the unique point lying on all three paths between pairs of reports.

## Proof sketch

Restricting to profiles supported on a leaf-to-leaf path gives a strategyproof onto rule on an interval, hence a generalized median voter scheme; strategyproofness glues these path schemes consistently at branching points.

For strong group strategyproofness, suppose a coalition changes the outcome from $a$ to $b \ne a$, and let $B$ be the component of the tree minus $a$ that contains $b$. Under an extended median voter scheme the facility lies in $B$ exactly when the agents reporting in $B$ form a winning coalition for the direction of $B$ at $a$, and winning coalitions are closed under supersets. The truthful agents in $B$ do not form one, since the truthful outcome is $a$; so the outcome can enter $B$ only if some coalition member whose true location $p_i$ lies outside $B$ (possibly $p_i = a$) reports a location in $B$. The path from $p_i$ to $b$ passes through $a$, so that member's cost rises strictly, from $d(p_i, a)$ to $d(p_i, a) + d(a, b)$. Hence no coalition can lower one member's cost without raising another's.

## Depends on

- [Extended median voter scheme on a tree](extended-median-voter-scheme-on-a-tree.md)
- [Facility-location mechanism on a metric space](facility-location-mechanism-on-a-metric-space.md)

## Proof depends on

- [Moulin's characterization of strategyproof location rules on an interval](moulins-characterization-of-strategyproof-location-rules-on-an-interval.md)

## Sources

- James Schummer and Rakesh V. Vohra, "Strategy-proof Location on a Network", Journal of Economic Theory, 2002.
- James Schummer and Rakesh V. Vohra, "Mechanism Design without Money", Algorithmic Game Theory, Cambridge University Press, 2007.
