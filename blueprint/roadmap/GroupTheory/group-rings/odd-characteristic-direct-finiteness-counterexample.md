# Failure of direct finiteness in a prescribed odd characteristic

Let $M=\binom{1200}{600}$ and let $p$ be the least prime factor of $(M!)^2+1$. Then $p$ is prime and odd, and there are a field $K$ of cardinality $p^4$ and characteristic $p$, a finitely generated group $G$ containing a nonidentity element of finite order, and $a,b\in K[G]$ with $ab=1$ and $ba\ne1$. The operator on $K^G$ given by $x\mapsto[g\mapsto\sum_u b_u x(gu)]$ is injective but not surjective. The sum uses the finite support of $b$; the claim is about this particular $p$, not all odd characteristics.

## Depends on

- Least prime factor, finite-field cardinality, and the group-ring operator on all configurations $K^G$.

## Proof depends on

- The odd-characteristic quadratic-tower construction and prescribed operators giving the one-sided pair. The arithmetic is elementary: $M\ge\binom{1200}{1}=1200$ by maximality of the central binomial coefficient, so $M!$ is even and $(M!)^2+1$ is odd and greater than one. Its smallest prime factor is therefore an odd prime.

## Expansion

Use the elementary primality and parity facts above without evaluating the factorial. Build the specific coefficient field and group, and transport the product identities to injectivity and failure of surjectivity on $K^G$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OddKaplansky.lean#L26-L28) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OddKaplansky.lean).
