# Crude rate of central death rates is total deaths over total exposure

Let $\iota$ be a finite set of categories (for example age groups), with real deaths $D_i$ and
positive exposures $N_i > 0$. The [crude rate](../../statistical-genetics/mendelian-randomization/weighted-mean.md) with sizes $N_i$ and with rates the
[central death rates](central-death-rate.md) $m_i = D_i / N_i$ is $(\sum_i D_i) / \sum_i N_i$, the
total deaths over the total exposure. The only hypothesis is the positivity of the exposures, under
which the central death rates are defined and $m_i N_i = D_i$; the deaths may have any sign. If
$\iota$ is empty, the total exposure is $0$ and both sides are $0$, by the convention $x / 0 = 0$.
