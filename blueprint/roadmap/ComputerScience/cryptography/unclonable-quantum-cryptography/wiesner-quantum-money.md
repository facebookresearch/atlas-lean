# Wiesner's private-key quantum money

In *Wiesner's quantum money* scheme, the bank chooses for each banknote a serial number $\mathsf{id}$ and secret strings $x,\theta\in\{0,1\}^{n}$ and issues the product state $|x\rangle_\theta=\bigotimes_{i=1}^{n}H^{\theta_i}|x_i\rangle$ of BB84 states, recording $(\mathsf{id},x,\theta)$. Verification measures each qubit in the basis $\theta_i$ and accepts iff the outcome equals $x$. A *counterfeiting attack* is a channel mapping one banknote to a state on two registers; it succeeds if both registers pass verification.

## Depends on

- [No-cloning theorem (linear form)](../../../QuantumInformation/quantum-operations/no-cloning-linear.md)

## Sources

- Stephen Wiesner, "Conjugate Coding", ACM SIGACT News (1983).
- Abel Molina, Thomas Vidick, John Watrous, "Optimal Counterfeiting Attacks and Generalizations for Wiesner's Quantum Money", TQC (2012), arXiv:1202.4010.
