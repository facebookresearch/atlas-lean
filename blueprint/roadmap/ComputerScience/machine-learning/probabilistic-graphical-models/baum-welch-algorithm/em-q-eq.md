# The Baum-Welch objective in terms of expected counts

Let $S$ and $O$ be finite sets, let
$T$ be a natural number, and let $x_1, \dots, x_N$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$ of
observations in $O$. For a valid hidden Markov model $h$ on states $S$ and observations $O$
(positive initial, transition and emission probabilities, each distribution summing to one), write
$p_h(x, z)$ for the path weight of the observations $x$ and a state path $z = (z_0, \dots, z_T)$
(the joint of the EM model of $h$) and $p_h(z \mid x) = p_h(x, z) / \sum_{z'} p_h(x, z')$ for the
posterior of the path, the sums ranging over all paths $z : \{0, \dots, T\} \to S$. Let
$I_s = \sum_n \sum_{z \,:\, z_0 = s} p_h(z \mid x_n)$,
$A_{ss'} = \sum_n \sum_z p_h(z \mid x_n) \, \#\{t < T : z_t = s,\ z_{t+1} = s'\}$ and
$E_{so} = \sum_n \sum_z p_h(z \mid x_n) \, \#\{t \le T : z_t = s,\ x_{n,t} = o\}$ be the expected
counts of initial states, transitions and emissions. Then for every valid hidden Markov model $h'$
with initial probabilities $\pi'_s$, transition probabilities $a'_{ss'}$ and emission
probabilities $b'_{so}$, the EM objective
$Q(h' \mid h) = \sum_n \sum_z p_h(z \mid x_n) \log p_{h'}(x_n, z)$ equals
$\sum_{s} I_s \log \pi'_s + \sum_{s, s'} A_{ss'} \log a'_{ss'} +
\sum_{s, o} E_{so} \log b'_{so}$.
