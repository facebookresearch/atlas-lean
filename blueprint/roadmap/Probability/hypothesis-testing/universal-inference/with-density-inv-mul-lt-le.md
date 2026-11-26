# Markov's inequality for a likelihood ratio

Let $\nu$ be a measure on $\mathcal{Y}$ and $q_0, q_1 : \mathcal{Y} \to [0, \infty]$ measurable functions with
$\int q_1 \, d\nu \le 1$ (no condition on $q_0$). For every $0 < \alpha < \infty$, the measure $q_0 \nu$ with density $q_0$
satisfies

$$(q_0 \nu)\bigl(\{y : \alpha^{-1} q_0(y) < q_1(y)\}\bigr) \le \alpha.$$

When $q_0$ is a probability density, this says that under the law $P_0 = q_0 \nu$ the likelihood ratio $q_1 / q_0$
exceeds $1/\alpha$ with probability at most $\alpha$. Written without division, on the event one has $q_0 \le \alpha q_1$,
so its $q_0\nu$-measure is at most $\alpha \int q_1 \, d\nu \le \alpha$; for a probability density $q_0$ this is Markov's
inequality for the likelihood ratio, whose mean under $P_0$ is at most $\int q_1 \, d\nu$. This is display (7) of Wasserman,
Ramdas and Balakrishnan for a fixed alternative $\psi$ ($q_1 = \mathcal L_0(\psi)$,
$q_0 = \mathcal L_0(\theta^*)$), together with the bound
$E_{\theta^*}[\mathcal L_0(\psi)/\mathcal L_0(\theta^*)] \le 1$ displayed just before it.

## Background

- [Neyman–Pearson lemma](../neyman-pearson-dominated-two-simple.md): the classical use of the same likelihood ratio between two simple hypotheses, where it gives the most powerful test rather than a level guarantee without regularity.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, arXiv:1912.11436v4 (21 October 2022); published in Proc. Natl. Acad. Sci. USA 117 (2020) 16880–16890. Theorem, remark and equation numbers refer to the arXiv version, which is the one read. Section 2, the bound before (6) and display (7).
