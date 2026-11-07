# Probability that a random pebbling configuration is solvable

Let $G$ be a simple graph on
a finite vertex set $V$ with $n$ vertices, let $w$ assign a natural-number cost to each unordered
pair of vertices, and let $t \ge 0$ be an integer. A configuration of $t$ pebbles is a function
$C : V \to \mathbb{N}$ with $\sum_{v \in V} C(v) = t$. The value is the number of configurations
of $t$ pebbles that are solvable with respect to $G$ and $w$, divided by the number of all
configurations of $t$ pebbles; that is, the probability that a configuration of $t$ pebbles
chosen uniformly at random is solvable. If there are no configurations of $t$ pebbles ($V$ empty
and $t > 0$), the value is $0$.

For $n \ge 1$ there are $\binom{n + t - 1}{t}$ configurations of $t$ pebbles (the space
$D_{G,t}$ of the source).

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 3.1 (configuration model).
