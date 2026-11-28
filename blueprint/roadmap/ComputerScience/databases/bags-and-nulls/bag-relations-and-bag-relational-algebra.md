# Bag relations and bag relational algebra

A bag relation over a schema $S$ is a finitely supported function assigning to each tuple over $S$ a
multiplicity in $\mathbb{N}$. The positive relational algebra acts on bag relations as follows:

- selection keeps the multiplicities of the tuples satisfying the condition and sets the others to $0$;
- projection sums the multiplicities of tuples with the same projection;
- natural join multiplies multiplicities;
- union adds multiplicities;
- renaming re-indexes attributes.

Set relations embed as bags with multiplicities in $\{0,1\}$. Bag relations with these operations are the
$\mathbb{N}$-relations of the semiring-annotated model of the positive relational algebra.

## Depends on

- [Tuple](../relational-algebra/tuple.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, §3, Definition 3.2 and Proposition 3.3 (bag semantics is the case of the semiring of natural numbers). <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
