# Consistency of maximum-likelihood tree estimation on ungapped alignments

Let $N = \{1, \dots, n\}$ be a set of taxa. A phylogenetic tree $T$ on $N$ (not necessarily binary) has leaves labelled bijectively by $N$ and a **positive** length on every edge; $d_T(a, b)$ is the path length between leaves $a, b$. On such trees,

$$D(T_1, T_2) = \max_{a, b \in N} \big| d_{T_1}(a, b) - d_{T_2}(a, b) \big|$$

is a metric (positivity of edge lengths is needed: with zero-length edges, distinct topologies can be at distance $0$).

Sites evolve independently along $T^*$ under the Jukes–Cantor substitution model. An ungapped alignment $A_m$ has $m$ columns; its normalized log-likelihood under $T$ is $L(A_m \mid T) = \frac{1}{m}\sum_{j=1}^m \log \Pr[A_m[\ast, j] \mid T]$, and $\mathrm{ML}(A_m) = \arg\max_T L(A_m \mid T)$.

**Lemma (uniform separation).** For every $\epsilon > 0$,

$$\Pr\Big[\sup_{T : D(T, T^*) > \epsilon} L(A_m \mid T) \ge L(A_m \mid T^*)\Big] \to 0 \qquad (m \to \infty).$$

**Theorem (consistency).** $D(\mathrm{ML}(A_m), T^*) \to 0$ with probability $1$ as $m \to \infty$.

The uniformity over the whole region $D(T, T^*) > \epsilon$ is the point: the classical arguments showing $L(A_m \mid T) < L(A_m \mid T^*)$ eventually, for each fixed $T \ne T^*$, do not by themselves exclude a sequence of maximizers that fails to converge to $T^*$.

## Expansion

Let $f^*_c$ be the probability of site pattern $c \in \Sigma^n$ under $T^*$ and $f_c = m_c/m$ its empirical frequency, so $f_c \to f^*_c$ almost surely and $L(A_m \mid T^*) \to \sum_c f^*_c \log f^*_c$. For a pair $a, b$ write $f^{ab}_{xy}$ for the empirical frequency of columns with $x$ at $a$ and $y$ at $b$, and $p^{\delta}_{xy}$ for the Jukes–Cantor probability of observing $(x, y)$ at two leaves at distance $\delta$. Writing $L(A \mid T) = \sum_c f_c \log p_c$, splitting each pattern into the letters at $a, b$ and the rest, and maximizing the conditional part by Gibbs' inequality gives, for any tree with $d_T(a,b) = \delta$, $L(A \mid T) \le \sum_c f_c \log f_c - D_{\mathrm{KL}}(\{f^{ab}_{xy}\} \,\|\, \{p^{\delta}_{xy}\})$. The pairwise log-likelihood $\delta \mapsto \sum_{xy} f^{ab}_{xy}\log p^{\delta}_{xy}$ is concave with maximizer $-\frac34 \log(1 - \frac43 f_{x \ne y})$, which tends to $d = d_{T^*}(a,b)$, so its supremum over $\delta \ge d + \epsilon$ (or $\delta \le d - \epsilon$) is eventually attained at $d \pm \epsilon$. Any $T$ with $D(T, T^*) > \epsilon$ has a pair with $|d_T(a,b) - d_{T^*}(a,b)| > \epsilon$, hence

$$\limsup_{m\to\infty} \sup_{T : D(T,T^*) > \epsilon} L(A_m \mid T) \le \sum_c f^*_c \log f^*_c - \min_{a, b \in N,\ s = \pm\epsilon} D_{\mathrm{KL}}\big(\{f^{ab}_{xy}\} \,\big\|\, \{p^{d+s}_{xy}\}\big)$$

almost surely. The pairwise Jukes–Cantor law determines the distance, so each divergence is strictly positive, which proves the lemma. If the maximizer lay at distance more than $\epsilon$ from $T^*$, its likelihood would be at least that of $T^*$; the lemma makes this event's probability vanish for every $\epsilon$, which gives the theorem.

## Sources

- J. Truszkowski and N. Goldman, "Maximum likelihood phylogenetic inference is consistent on multiple sequence alignments, with or without gaps", Systematic Biology 65(2) (2016), 328–333, Preliminaries (metric $D$, Theorem 1, Lemma 1) and the section on a new proof for ungapped alignments (Lemmas 2–3, proofs of Lemma 1 and Theorem 1), <https://doi.org/10.1093/sysbio/syv089> (PMC4748752).
