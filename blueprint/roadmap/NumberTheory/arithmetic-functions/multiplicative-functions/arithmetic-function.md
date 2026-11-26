# Arithmetic function on the positive integers

An arithmetic function is a function $f$ that assigns to each positive integer $n$ a complex number $f(n)$. Mathlib encodes such a function as a function on all natural numbers that vanishes at $0$, with values in any type with a zero. For a type $R$ with a distinguished element $0$, an *arithmetic function* with values in $R$ is a function $f \colon \mathbb{N} \to R$ with $f(0) = 0$. No additive or multiplicative property is required; in particular $f$ need not be multiplicative, and the definition does not involve Dirichlet convolution. Extending a function on the positive integers by the value $0$ at $0$, and restricting an arithmetic function to the positive integers, are inverse bijections between the functions from the positive integers to $R$ and Mathlib's arithmetic functions. Taking $R = \mathbb{C}$ gives the familiar definition.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for functions that send $0$ to $0$: `ZeroHom`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Hom/Defs.lean#L85-L89.
