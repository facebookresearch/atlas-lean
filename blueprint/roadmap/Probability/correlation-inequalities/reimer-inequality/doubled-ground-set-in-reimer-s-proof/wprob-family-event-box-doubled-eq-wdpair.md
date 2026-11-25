# Weighted disjoint pairs as a doubled-weight probability

Let $\alpha$ be a finite set, $w : \alpha \times \{0,1\} \to \mathbb{R}$ arbitrary and $\mathcal{A}, \mathcal{B}$ families of subsets of $\alpha$. Let $\tilde w$ be the [doubled weight](double-weight.md) on $\alpha \sqcup \alpha$. Then the $\tilde w$-weighted probability of the event that the support of a configuration lies in the [doubled family](box-doubled.md) $\mathcal{A} \boxtimes \mathcal{B}$ equals the [weighted number of disjoint pairs](../weighted-disjoint-pair-sums/wdpairs.md):

$$\sum_{\omega :\ \operatorname{supp}\omega \in \mathcal{A} \boxtimes \mathcal{B}} \ \prod_{x \in \alpha \sqcup \alpha} \tilde w_x(\omega(x)) = \sum_{\substack{(S, T) \in \mathcal{A} \times \mathcal{B} \\ S \cap T = \emptyset}} w(S)\, w(T).$$
