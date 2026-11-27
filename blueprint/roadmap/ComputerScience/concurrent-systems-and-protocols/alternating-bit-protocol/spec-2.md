# Recursive specification of the alternating-bit protocol with data

There is a separate
process constant $X_s$ for each state $s$ of each of five components: the sender, the lossy data
channel, the receiver, the lossy acknowledgement channel and the one-place buffer of bits. If
$(a_1, s_1), \dots, (a_n, s_n)$ are the listed transitions of $s$ in its component, then the body
of $X_s$ is the choice of prefixes $a_1.X_{s_1} + (a_2.X_{s_2} + \dots + (a_n.X_{s_n} + 0))$,
where each $X_{s_i}$ is the constant of the same component and $0$ is the inactive process; the
body is $0$ when $s$ has no listed transitions.
