# Lie Markov models with full nucleotide symmetry

**Symmetry of a model (Definition 4.5).** A Lie Markov model $\mathfrak L\subseteq\mathfrak L_{GM}$ has the symmetry of $G\le\mathfrak S_n$ if it has a basis $\{L_1,\dots,L_d\}$ permuted by conjugation, $K_\sigma\{L_1,\dots,L_d\}K_\sigma^{-1}=\{L_1,\dots,L_d\}$ for all $\sigma\in G$. Then any inference method gives results that are equivariant under relabelling nucleotides by $G$, since a nucleotide permutation is absorbed by a permutation of parameters. The general Markov model $\langle L_{ij}\rangle$ has $\mathfrak S_n$ symmetry.

**Decomposition.** For four states, $\mathfrak L_{GM}$ (dimension $12$) decomposes into irreducible $\mathfrak S_4$-modules as

$$\mathfrak L_{GM}\cong\{4\}\oplus 2\{31\}\oplus\{2^2\}\oplus\{21^2\},$$

with $\{4\}$ the trivial and $\{1^4\}$ the sign representation. A model with $\mathfrak S_4$ symmetry is a sum of permutation modules $\langle\mathfrak S_4/H\rangle$ that embeds in this decomposition and is closed under brackets.

**Theorem 6.1.** On four character states there are exactly five Lie Markov models with $\mathfrak S_4$ symmetry, of dimensions $1,3,4,6,12$:

| Model | Dimension | Brackets |
|---|---|---|
| Jukes–Cantor | 1 | none |
| Kimura 3ST | 3 | abelian: $[L_\alpha,L_\beta]=[L_\alpha,L_\gamma]=[L_\beta,L_\gamma]=0$ |
| Felsenstein 81 | 4 | $[R_i,R_j]=R_i-R_j$ |
| K3ST + F81 | 6 | $[L_{ij\mid kl},R_i]=R_j-R_i$ |
| general Markov | 12 | $[L_{ij},L_{kl}]=(L_{il}-L_{jl})(\delta_{jk}-\delta_{jl})-(L_{kj}-L_{lj})(\delta_{il}-\delta_{jl})$ |

Here $L_\alpha=L_{12\mid 34}$, $L_\beta=L_{13\mid 24}$, $L_\gamma=L_{14\mid 23}$ are the Kimura generators and $R_i$ is the rate matrix with all substitutions into state $i$ at equal rate. In particular no eight-dimensional $\mathfrak S_4$-symmetric model exists, the K3ST+F81 model is neither group-based nor equivariant, and the largest symmetry of the Kimura 3ST model is all of $\mathfrak S_4$.

## Expansion

Projection operators built from the $\mathfrak S_4$ character table split $\mathfrak L_{GM}\cong\mathbb C^4\otimes\mathbb C^4$ minus the diagonal; since $\mathbb C^4\cong\{4\}\oplus\{31\}$, the tensor square is $2\{4\}\oplus3\{31\}\oplus\{2^2\}\oplus\{21^2\}$ and removing the diagonal copy of $\{4\}\oplus\{31\}$ gives the decomposition above. Each candidate model of dimension $d$ is a permutation module $\bigoplus\langle\mathfrak S_4/H_i\rangle$ whose irreducible content fits inside $\mathfrak L_{GM}$; permutation modules containing the sign representation $\{1^4\}$ are excluded because $\mathfrak L_{GM}$ does not contain it, which rules out dimension $8$. The remaining candidates are checked for bracket closure, leaving the five models listed. The same procedure gives full classifications for two and three states.

## Depends on

- [Equivariant and group-based models are Lie Markov models](equivariant-and-group-based-models-are-lie-markov-models.md)

## Sources

- Jeremy G. Sumner, Jesús Fernández-Sánchez and Peter D. Jarvis, "Lie Markov models", arXiv:1105.4680 (2011), Section 4 (Definition 4.5 and the result on the symmetry of the general model), Section 5 (general scheme), Section 6 (decomposition of the general Markov model, Theorem 6.1 and its table), <https://doi.org/10.48550/arXiv.1105.4680>. Published version: Journal of Theoretical Biology 298 (2012), 16–31, <https://doi.org/10.1016/j.jtbi.2011.12.017>; locators above refer to the arXiv version.
