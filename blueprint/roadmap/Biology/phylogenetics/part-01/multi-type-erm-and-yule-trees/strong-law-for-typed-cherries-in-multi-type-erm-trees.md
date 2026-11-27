# Strong law for typed cherries in multi-type ERM trees

**Model (two-type ERM tree).** Start from a single leaf of type $1$ or $2$. At each step pick a leaf uniformly at random and attach two new leaves to it; a picked leaf of type $i$ receives leaves of types $(j_1,j_2)$, $j_1\le j_2$, with probability $q_i^{j_1j_2}$, where $\sum_{j_1\le j_2}q_i^{j_1j_2}=1$ and $q_1^{11},q_2^{22}\neq 1$. The shape is the equal-rates-Markov (Yule) tree shape and the types form a Markov field on it. A cherry of type $ij_1j_2$ is a branch point of type $i$ whose two children are leaves of types $j_1,j_2$; let $C_i^{j_1j_2}(n)$ be the number of such cherries and $N_1(n)$ the number of type-$1$ leaves in a tree with $n$ leaves. Put

$$c_1 = 2q_1^{11}+q_1^{12}, \qquad c_2 = 2q_2^{11}+q_2^{12}.$$

**Mean number of type-1 leaves (Lemma 2.1).** If $c_1-c_2\notin\{-2,2\}$, then for $n\ge 3$

$$\mathbb{E}[N_1(n)] = \frac{c_2\,n}{2-c_1+c_2} - \frac{\bigl(2c_2-(2-c_1+c_2)\nu_1(2)\bigr)\,\Gamma(n-1+c_1-c_2)}{(2-c_1+c_2)\,\Gamma(c_1-c_2+2)\,\Gamma(n)},$$

with $\nu_1(2)=c_1$ if the initial leaf has type $1$ and $\nu_1(2)=c_2$ otherwise.

**Theorem (strong law, Theorem 2.6).** Assume every cherry type can eventually be attached to every other (irreducibility of the cherry state space). Then, almost surely as $n\to\infty$,

$$\frac{C_1^{j_1j_2}(n)}{n}\to\frac{q_1^{j_1j_2}\,c_2}{3(2-c_1+c_2)}, \qquad \frac{C_2^{j_1j_2}(n)}{n}\to\frac{q_2^{j_1j_2}\,(2-c_1)}{3(2-c_1+c_2)},$$

and the counts of the four pendant types also have explicit almost-sure limits. The total cherry density is $1/3$, as in the single-type ERM tree.

**Fluctuations (Theorem 2.9).** If moreover $c_1-c_2\neq 0$ and $c_1-c_2<3/2$, the centred vector of cherry and pendant counts divided by $\sqrt n$ is asymptotically multivariate normal; at the critical value $c_1-c_2=3/2$ the normalization acquires a logarithmic factor.

**Inference (Corollary 2.11).** For a large tree with observed cherry densities $x_{ij_1j_2}=C_i^{j_1j_2}(n)/n$, the propagation probabilities are recovered as

$$q_i^{j_1j_2} \approx \frac{x_{ij_1j_2}}{x_{i11}+x_{i12}+x_{i22}}, \qquad i=1,2,$$

provided some cherry with a type-$i$ branch point is observed.

## Expansion

Cherries and pendants of each type are the ball colours of an extended Pólya urn with $10$ colours: a cherry is picked with weight $2$ and a pendant with weight $1$, since a cherry holds two leaves. The urn's generating matrix has eigenvalues $\lambda_1=1$, $\lambda_2=c_1-c_2-1$, $-1$ (twice) and $-2$ (six times). Janson's limit theorems for irreducible urns give almost-sure convergence of the counts divided by $n$ to the normalized right Perron eigenvector, and a Gaussian limit at scale $\sqrt n$ when $\operatorname{Re}\lambda_2<\lambda_1/2$, i.e. $c_1-c_2<3/2$. The inference rule is the law of large numbers read backwards: among cherries rooted at a type-$i$ node, the fraction of type $ij_1j_2$ converges to $q_i^{j_1j_2}$. The mean formula comes from the recursion $\nu_1(n+1)=c_2+\frac{1}{n}(n+c_1-c_2-1)\nu_1(n)$.

## Sources

- Lea Popovic and Mariolys Rivas, "Topology and inference for multi-type Yule trees", arXiv:1409.2957 (2014), Section 2 (Lemma 2.1, Theorems 2.6 and 2.9, Corollary 2.11), <https://doi.org/10.48550/arXiv.1409.2957>. Published version: "Topology and inference for Yule trees with multiple states", Journal of Mathematical Biology 73(5) (2016), 1251–1291, <https://doi.org/10.1007/s00285-016-0992-6>; locators above refer to the arXiv version.
