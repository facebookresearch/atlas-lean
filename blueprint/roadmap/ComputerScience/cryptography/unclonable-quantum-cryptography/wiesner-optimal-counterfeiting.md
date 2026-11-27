# Optimal counterfeiting probability for Wiesner's quantum money is (3/4)^n

For Wiesner's scheme with $n$ qubits and no access to the bank's verification oracle, the maximal probability that a (computationally unbounded) counterfeiter, given one banknote, produces two banknotes both accepted by honest verification equals $(3/4)^{n}$. The optimum for a single qubit is $3/4$, achieved by a specific cloning channel, and the $n$-qubit optimum is attained by applying it independently to each qubit (parallel repetition is perfect for this game).

## Proof sketch

Write the success probability as $\langle Q,\Phi\rangle$ for the Choi operator $\Phi$ of the counterfeiting channel and $Q=\frac{1}{4^{n}}\sum_{x,\theta}|x\rangle\langle x|_\theta^{\otimes 2}\otimes\overline{|x\rangle\langle x|_\theta}$; the optimum is a semidefinite program. Exhibit a primal solution of value $3/4$ per qubit and a dual solution certifying the matching upper bound; the product structure of $Q$ makes the dual multiplicative, giving $(3/4)^{n}$.

## Depends on

- [Wiesner's private-key quantum money](wiesner-quantum-money.md)

## Proof depends on

- [No-cloning theorem for two states](../../../QuantumInformation/quantum-operations/no-cloning-two-state.md)

## Sources

- Abel Molina, Thomas Vidick, John Watrous, "Optimal Counterfeiting Attacks and Generalizations for Wiesner's Quantum Money", TQC (2012), arXiv:1202.4010.
