# Convergence implies zero-stability

A [convergent](convergence-of-a-linear-multistep-method.md) [linear multistep method](linear-multistep-method.md) is [zero-stable](zero-stability.md).

The proof applies the method to $y' = 0$, $y(0) = 0$, whose solution is $y \equiv 0$, so that convergence forces every solution of $\sum_{j=0}^{k} \alpha_j y_{n+j} = 0$ with starting values tending to $0$ to satisfy $y_n \to 0$ as $h \to 0$ with $nh = x$ fixed. For a zero $z = re^{i\varphi}$ of $\rho$, the solution $y_n = h r^n \cos n\varphi$ shows $r \le 1$; for a multiple zero with $r = 1$, the solution $y_n = h^{1/2} n r^n \cos n\varphi$ gives a contradiction. So the method satisfies the root condition, hence it is zero-stable.

## Depends on

- [Convergence of a linear multistep method](convergence-of-a-linear-multistep-method.md)
- [Zero-stability](zero-stability.md)

## Proof depends on

- [Root condition](root-condition.md)
- [Zero-stability is equivalent to the root condition](zero-stability-iff-root-condition.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4.1, Theorem 7 and its proof. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
