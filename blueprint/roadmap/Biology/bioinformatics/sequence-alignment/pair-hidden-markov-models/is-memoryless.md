# Memoryless pair HMM

A real [pair HMM](pair-hmm.md) is memoryless with transition weights $\pi(s)$ and end weight $\tau$ if

- $\pi_0(s) = \pi(s)$ for every emitting state $s$;
- $t(s, s') = \pi(s')$ for all emitting states $s, s'$;
- $\tau(s) = \tau$ for every emitting state $s$;
- $\tau_0 = \tau$.
