# Stage covariance in the time-window-of-integration model

**Model.** In the time-window-of-integration (TWIN) model of crossmodal reaction time, the response time is the sum of a first-stage time $W_1$ (a race of peripheral unimodal activations) and a second-stage time $W_2$ (neural integration and response preparation),

$$RT_{VA}=W_1+W_2 ,$$

with $W_1,W_2$ on one probability space. Let $I$ be the event that multisensory integration occurs (all first-stage processes finish within the time window), $\pi=\mathbb P(I)\in(0,1)$, and assume $W_1$ and $W_2$ are conditionally independent given $I$ and given $I^c$, with finite means. Then

$$H(w_1,w_2)=\pi\,F_I(w_1)G_I(w_2)+(1-\pi)\,F_{I^c}(w_1)G_{I^c}(w_2),$$

where $F_\cdot$ and $G_\cdot$ are the conditional distribution functions of $W_1$ and $W_2$.

**Proposition.** If $W_1$ and $W_2$ have finite second moments, then

$$\operatorname{Cov}(W_1,W_2)=\pi(1-\pi)\big(\mathbb E[W_1\mid I^c]-\mathbb E[W_1\mid I]\big)\big(\mathbb E[W_2\mid I^c]-\mathbb E[W_2\mid I]\big).$$

In particular the dependence between the two stages is generated entirely by the integration event, and it can be positive, negative or zero depending on how integration shifts the two stage means.

## Proof sketch

Conditional independence gives $\mathbb E[W_1W_2]=\pi m_1^Im_2^I+(1-\pi)m_1^cm_2^c$, with $m_k^I=\mathbb E[W_k\mid I]$ and $m_k^c=\mathbb E[W_k\mid I^c]$, while $\mathbb E W_k=\pi m_k^I+(1-\pi)m_k^c$. Subtracting the product of means leaves $\pi(1-\pi)(m_1^I-m_1^c)(m_2^I-m_2^c)$. Equivalently, Hoeffding's identity $\operatorname{Cov}(W_1,W_2)=\iint\big(H(s,t)-H_1(s)H_2(t)\big)\,ds\,dt$ applied to the two-component product mixture gives the same expression.

## Depends on

- [Race model inequality from the Fréchet–Hoeffding bounds](race-model-inequality-from-frechet-hoeffding-bounds.md)

## Sources

- Hans Colonius, "An invitation to coupling and copulas: With applications to multisensory modeling", *Journal of Mathematical Psychology* 74 (2016), 2–10, <https://doi.org/10.1016/j.jmp.2016.02.004>. Preprint version: arXiv:1511.05303 (2015), Section 3.6 (Hoeffding's identity) and Section 4 (Example 21), <https://doi.org/10.48550/arXiv.1511.05303>.
