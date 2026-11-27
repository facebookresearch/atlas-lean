# Fano's method: lower bound on the error of multiple hypothesis testing

Let $V$ be a finite set with $|V| \ge 2$, draw $V$ uniformly, and let $X \sim P_V$. For every test $\psi$ with average error $P_e = \frac1{|V|}\sum_v P_v[\psi(X) \ne v]$,

$$
\log_2 |V| - I(X;V) \le h_2(P_e) + P_e \log_2(|V| - 1),
$$

where $h_2$ is the binary entropy in bits and $I$ is in bits. Consequently, with $I$ in nats, $P_e \ge 1 - (I(X;V) + \log 2)/\log |V|$. If $\frac1{|V|}\sum_v D(P_v\|Q) \le \beta$ for some center $Q$ (or $\frac1{|V|^2}\sum_{v,w} D(P_v\|P_w) \le \beta$), then $P_e \ge 1 - (\beta + \log 2)/\log|V|$.

## Proof sketch

Fano's inequality bounds $H(V \mid \psi(X))$ by $h_2(P_e) + P_e\log_2(|V|-1)$, and data processing gives $H(V\mid\psi(X)) \ge \log_2|V| - I(X;V)$. Bounding $h_2 \le 1$ and $\log(|V|-1) \le \log|V|$ gives the closed form, and the mutual-information bound by divergences gives the KL forms.

## Depends on

- [Fano's inequality](../../../../InformationTheory/information-inequalities/fano-s-inequality/fano-inequality.md)
- [Mutual information of a finite joint law](../../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/measure-mutual-information-to-measure.md)
- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

- [Fano's inequality](../../../../InformationTheory/information-inequalities/fano-s-inequality/fano-inequality.md)
- [Mutual information is bounded by the average pairwise divergence](mutual-information-kl-center-bound.md)

## Sources

- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
