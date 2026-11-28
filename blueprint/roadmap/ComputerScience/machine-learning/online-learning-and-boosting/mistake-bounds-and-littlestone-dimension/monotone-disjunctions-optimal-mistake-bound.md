# The optimal mistake bound for k-literal monotone disjunctions is $\Theta(k \log(n/k))$

Let $\mathcal{D}_{n,k}$ be the class of monotone disjunctions of exactly $k$ of $n$ Boolean variables. Then $\mathcal{D}_{n,k}$ shatters a set of $k\lfloor\log_2(n/k)\rfloor$ instances, so

$$
k\lfloor\log_2(n/k)\rfloor \le \mathrm{opt}(\mathcal{D}_{n,k}),
$$

and for $1 \le k$, WINNOW1 with $\alpha = 2$, $\theta = n/k$ gives $\mathrm{opt}(\mathcal{D}_{n,k}) \le \lfloor 2k\log_2(n/k) + 3k\rfloor$. For $1 \le k$ and $2k \le n$ both bounds are $\Theta(k\log(n/k))$, so Winnow is optimal up to a constant factor.

## Proof sketch

With $r = \lfloor\log_2(n/k)\rfloor$, split $k2^r \le n$ variables into $k$ groups indexed by subsets of $\{1,\ldots,r\}$. Instance $(j, s)$ sets exactly the variables of group $j$ whose index contains $s$. For any set $U$ of instances, the disjunction taking from each group $j$ the variable indexed by $\{s : (j,s) \in U\}$ is $1$ exactly on $U$, so the $kr$ instances are shattered and VC dimension lower-bounds the mistake bound. The upper bound is Winnow's specialization.

## Depends on

- [Winnow (WINNOW1) for monotone disjunctions](winnow1-algorithm.md)
- [The Littlestone dimension is the optimal mistake bound](../the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Littlestone's Winnow mistake bound $\alpha k(\log_\alpha\theta + 1) + n/\theta$](winnow-mistake-bound.md)
- [VC dimension is at most Littlestone dimension and mistake-bound comparisons](natarajan-vc-littlestone-dimension-comparisons.md)

## Sources

- Nick Littlestone, "Learning Quickly When Irrelevant Attributes Abound: A New Linear-Threshold Algorithm", Machine Learning 2(4), 1988.
