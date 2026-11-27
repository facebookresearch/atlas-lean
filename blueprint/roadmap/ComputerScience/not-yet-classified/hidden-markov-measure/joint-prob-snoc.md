# One-step recurrence for the hidden Markov joint law

For a hidden Markov model with transition weights $A(s, s')$ and emission weights $B(s, o)$, a state path $z_0, \dots, z_t$ and observations $x_0, \dots, x_t$, extending by a state $s$ and an observation $o$ gives

$$p(z_0, \dots, z_t, s;\ x_0, \dots, x_t, o) = p(z_0, \dots, z_t;\ x_0, \dots, x_t)\, A(z_t, s)\, B(s, o).$$
