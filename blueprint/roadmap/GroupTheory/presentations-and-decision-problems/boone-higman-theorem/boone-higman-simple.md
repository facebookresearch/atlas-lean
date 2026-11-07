# Kuznetsov's theorem on finitely presented simple groups

Let $G$ be a simple group, let
$F_n$ be the free group on $n$ generators, and let $\varphi \colon F_n \to G$ be a surjective
homomorphism whose kernel is the normal closure of finitely many elements. Then the word problem
of $G$ with respect to $\varphi$ is solvable: there is an algorithm that decides, for every word
$w$ in the $n$ generators and their inverses, whether $\varphi(w) = 1$.

## Sources

- A.V. Kuznetsov, 'Algorithms as operations in algebraic systems', Uspekhi Mat. Nauk 13 (1958) 240–241 (Russian); W.W. Boone and G. Higman, 'An algebraic characterization of groups with soluble word problem', J. Austral. Math. Soc. 18 (1974) 41–53. §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `boone_higman_simple` of the lean-eval benchmark.
