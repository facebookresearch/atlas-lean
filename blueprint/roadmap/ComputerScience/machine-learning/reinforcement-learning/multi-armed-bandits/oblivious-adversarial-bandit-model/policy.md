# Policy for an oblivious adversarial bandit

A policy for a $k$-armed oblivious adversarial bandit is a sequence $\pi = (\pi_t)_{t \ge 1}$ that gives, for each round
$t$ and each history $h = (a_1, r_1, \dots, a_{t-1}, r_{t-1})$ of the arms chosen and the real rewards observed in the
earlier rounds, a probability mass function $\pi_t(\cdot \mid h)$ on the arms $\{1, \dots, k\}$: the law of the arm
chosen in round $t$. The source's rewards lie in $[0, 1]$; real rewards let the policy play on every real reward table.
The sequence runs over all rounds, so the same policy serves every horizon. No measurability condition is imposed: on a
fixed reward table only finitely many histories occur. In the formal statement, arms and rounds are counted from $0$,
the arm $i$ being stored as $i - 1$: the distribution indexed by $t$ reads the histories of $t$ rounds, and it is
$\pi_{t+1}$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 11.1 (a policy maps the histories in $([k] \times [0, 1])^*$ to distributions over the arms, regardless of measurability) and Section 11.5, Note 12 (no measurability condition is needed). <https://tor-lattimore.com/downloads/book/book.pdf>
