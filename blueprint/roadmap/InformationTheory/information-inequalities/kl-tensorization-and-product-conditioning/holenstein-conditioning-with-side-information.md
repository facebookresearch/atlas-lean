# Holenstein's conditioning lemma with side information

Let $T$, $V$ and $\mathcal{U}$ be finite sets, and let $P_{T U^k V} = P_T\, P_{U_1 \mid T} \cdots P_{U_k \mid T}\, P_{V \mid T U^k}$ be a distribution on $T \times \mathcal{U}^k \times V$: given $t$, the coordinates $U_1, \dots, U_k$ are independent, and $V$ is arbitrary side information. Let $W$ be an event with $\Pr[W] > 0$, let $V^* = \{v \in V : P_{V \mid W}(v) > 0\}$, and write $\delta$ for statistical distance. Then

$$
\sum_{j=1}^{k} \delta\Big(P_{T U_j V \mid W},\ P_{T V \mid W}\, P_{U_j \mid T}\Big) \le \sqrt{k}\,\sqrt{\log_2|V^*| + \log_2\frac{1}{\Pr[W]}},
$$

where $P_{TV \mid W}\, P_{U_j \mid T}$ draws $(t, v)$ from the conditional law given $W$ and then $u_j$ afresh from $P_{U_j \mid T = t}$. Also, if $P_{U^k} = P_{U_1} \cdots P_{U_k}$ is a product distribution on $\mathcal{U}^k$ and $W$ an event, then

$$
\Pr[W] \le 2^{-\sum_{j=1}^{k} \delta(P_{U_j \mid W},\, P_{U_j})^2}.
$$

## Proof sketch

For the second claim, the conditioned law of $U^k$ has relative entropy at most $\log_2(1/\Pr[W])$ from the product, relative entropy is superadditive over the coordinates of a product reference law, and each coordinate's relative entropy bounds its squared statistical distance. Summing with $(\sum_j a_j)^2 \le k\sum_j a_j^2$ gives $\sum_j \delta(P_{U_j \mid W}, P_{U_j}) \le \sqrt{k\log_2(1/\Pr[W])}$. For the main claim, fix $(t, v)$ and apply this to $P_{U^k \mid T = t, V = v, W}$ against $P_{U^k \mid T = t}$ with the event $(V = v) \wedge W$; Jensen's inequality averages the bounds over $(t, v)$, which costs the term $\log_2|V^*|$. The source's logarithm is base $2$, as its exponential form of the second claim shows.

The following natural-log forms are derived here and are not stated in the cited source. Using the sharp Pinsker inequality $D \ge 2\delta^2$ (in nats) instead, the same steps give $\sum_j \delta(P_{U_j \mid W}, P_{U_j})^2 \le \frac12\ln(1/\Pr[W])$ and

$$
\sum_{j=1}^{k} \delta\Big(P_{T U_j V \mid W},\ P_{T V \mid W}\, P_{U_j \mid T}\Big) \le \sqrt{\frac{k}{2}\ln\frac{|V|}{\Pr[W]}},
$$

using $\mathbb{E}\big[1/\Pr[V = v, W \mid t]\big] \le |V|/\Pr[W]$ in the averaging step.

## Depends on

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Raz's conditioning lemma for product distributions](raz-conditioning-lemma.md)

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009, Section 2.1, equation (2.2), and Section 4, Lemma 4.1, inequality (4.2), Lemma 4.2 and Corollary 4.3.
