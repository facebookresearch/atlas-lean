# The ChromHMM M-step

For $T$, sequences $x^{(1)}, \dots, x^{(N)}$ and a [valid parameter](valid.md) $\theta$, the M-step returns the parameters with

- initial weights $\hat\pi(s) = \frac1N \times$ (expected number of sequences starting in $s$);
- transition weights $\hat a(s, s') = A(s, s') / \sum_{s''} A(s, s'')$, with $A(s, s')$ the expected number of transitions $s \to s'$;
- mark probabilities $\hat p_{s,j} = m_1(s, j) / (m_1(s, j) + m_0(s, j))$, the [factored update](factored-update.md) of the expected emission counts,

expectations under the posterior of the state paths given each sequence, with the convention $x/0 = 0$.
