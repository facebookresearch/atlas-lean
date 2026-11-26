# Finite abelian Fourier complexity and geometric-border feedback lower bound

Let $G$ be a finite abelian group in additive notation of order $n\ge2$. Let $K$ be a field in which $n$ is nonzero and which contains a primitive root of unity of order equal to the exponent of $G$. Write $\widehat G$ for the homomorphisms $G\to K^\times$. The forward transform is the matrix with row $\chi$, column $g$, and entry $\chi(g)$; the normalized inverse has row $g$, column $\chi$, and entry $n^{-1}\chi(-g)$.

A binary linear gate forms $au+bv$ from two input or prior gate wires, with coefficients in $K$. Each output is zero or a scaled available wire at no gate cost. Let $s(M)$ be the least number of such gates realizing a matrix $M$ (realization is equality of the actions on standard basis inputs). A regular binary feedback system with $S$ states has one such two-wire equation per state, now permitting any state or input wire, plus the same free readouts. In matrix form its equations are $z=Az+Bx$, $y=Cz+Dx$ with $\det(I-A)\ne0$, and its transfer is $D+C(I-A)^{-1}B$. The transfer with at most $S$ states is allowed to vary over $\overline K$. A matrix over $K$ is in their geometric border if, after scalar extension, every polynomial in the matrix entries vanishing on all such transfers also vanishes there.

There is a real $c>0$ such that for every real $\varepsilon>0$ there is $C>0$ for which, for all $G,K$ as above and for **both** the forward and inverse matrices $M$,

$$
c n\sqrt{\log_2 n}\le s(M)\le C n(1+\log_2 n)^{1/2+\varepsilon}.
$$

If either matrix is in the geometric border of regular transfers with at most $S$ states, then $c n\sqrt{\log_2 n}\le S$. In particular $c$ is fixed before the slack, field, group, and direction are chosen.

## Depends on

- Finite abelian groups, their field-valued characters, and the binary-gate size and feedback transfer defined above. These are exact arithmetic models, not declared-cost FFT bounds.

## Proof depends on

- Exact-circuit constructions with a common slack-dependent constant and a characteristic-uniform lower bound stable under the specified Zariski closure of regular feedback transfers.

## Expansion

Separate realizability and free readouts from the feedback and geometric-border notions; prove the determinant/transfer relation and the interpretation over an algebraic closure. Break down the upper and lower estimates without bounding coefficients or replacing the geometric border by an ordinary metric limit.

## Related topics

- The [complex cyclic DFT sum](dft-sum.md) specializes the forward character matrix when the group is cyclic and the field is $\mathbb C$.

## Sources

- OpenAI, [ExactFourier.lean, binary linear and feedback models, and `fourierComplexity`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ExactFourier.lean#L64-L246).
