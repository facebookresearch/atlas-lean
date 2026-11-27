# Root condition

A [linear multistep method](linear-multistep-method.md) with first characteristic polynomial $\rho(z) = \sum_{j=0}^{k} \alpha_j z^j$ satisfies the *root condition* if every complex zero of $\rho$ lies in the closed unit disc $|z| \le 1$ and every zero on the unit circle $|z| = 1$ is simple.

For example, Euler's explicit and implicit methods and the trapezium rule have $\rho(z) = z - 1$ and satisfy it, while $\rho(z) = (z - 1)^2$ does not.

## Depends on

- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.2, the paragraph after Theorem 6, and Example 4. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
