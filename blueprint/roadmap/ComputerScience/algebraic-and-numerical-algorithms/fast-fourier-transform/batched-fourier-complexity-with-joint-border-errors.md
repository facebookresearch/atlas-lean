# Batched Fourier complexity with joint rank and support errors

For a finite abelian group $G$ of order $n\ge2$, call a field $K$ admissible for $G$ if $n$ is nonzero in $K$ and $K$ contains a primitive root of unity of order equal to the exponent of $G$. Write $\widehat G$ for the homomorphisms $G\to K^\times$. The forward transform is the matrix with row $\chi$, column $g$, and entry $\chi(g)$; the normalized inverse has row $g$, column $\chi$, and entry $n^{-1}\chi(-g)$.

A binary linear gate forms $au+bv$ from two input or prior gate wires, with coefficients in $K$. Each output is zero or a scaled available wire at no gate cost. Let $s(M)$ be the least number of such gates realizing a matrix $M$ (realization is equality of the actions on standard basis inputs). A regular binary feedback system with $S$ states has one such two-wire equation per state, now permitting any state or input wire, plus the same free readouts. In matrix form its equations are $z=Az+Bx$, $y=Cz+Dx$ with $\det(I-A)\ne0$, and its transfer is $D+C(I-A)^{-1}B$. The transfer with at most $S$ states is allowed to vary over $\overline K$. A matrix over $K$ is in their geometric border if, after scalar extension, every polynomial in the matrix entries vanishing on all such transfers also vanishes there.

There are absolute reals $c,\beta,\eta>0$ such that for each real $\varepsilon>0$ some $C>0$ has the following property. For every $J\ge1$, $n\ge2$ and field $K$, take a batch of $J$ abelian groups of order $n$, each admissible over $K$ as specified above. In each block independently choose the forward or normalized inverse direction and order the points and characters bijectively by $[n]$. Let $T$ be the $Jn$ by $Jn$ block diagonal matrix of these transforms; gates may mix wires across all blocks. Put $h=Jn$ and $\lambda=\sqrt{\log_2 n}$. Then

$$
c h\lambda\le s(T)\le C h(1+\log_2 n)^{1/2+\varepsilon}.
$$

Moreover, for each natural $S$, if the scalar extension of $T$ lies in the Zariski closure of matrices $A+B+Z$ over $\overline K$, where $A$ is a regular binary feedback transfer with at most $S$ states, $\operatorname{rank}(B)\le\beta h$ and $Z$ has at most $\eta h\,2^{\lambda/8}$ nonzero entries, then $c h\lambda\le S$. These two errors act on the whole matrix, including off-block entries; the closure is of the joint set of sums.

## Depends on

- The field admissibility, exact gate size, direct-sum, and regular transfer definitions above.

## Proof depends on

- A shared-gate lower bound uniform over mixed directions and groups, robust under joint low-rank and sparse errors, and an exact upper bound with a constant independent of $J$.

## Expansion

Define both error measures across the entire transfer and show the exact inclusion and compatibility properties of the joint Zariski closure. Establish the lower bound without assuming each gate or each error lies in one block. Single-transform estimates do not give a direct sum lower bound in this model by themselves.

## Sources

- OpenAI, [ExactFourier.lean, batched transforms, joint border and `batchedFourierComplexity`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ExactFourier.lean#L64-L311).
