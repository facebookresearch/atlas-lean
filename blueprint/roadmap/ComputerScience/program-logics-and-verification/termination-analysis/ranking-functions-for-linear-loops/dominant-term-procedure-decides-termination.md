# Dominant-term procedure decides termination

Let $P_4 : \mathbf{while}\ (B_1 y_1 + \dots + B_r y_r > 0)\ \{\, y_1 := J_1 y_1; \dots; y_r := J_r y_r \,\}$ be a homogeneous linear loop whose blocks $J_i$ are Jordan blocks for positive real eigenvalues. Write $\mathrm{Cond}_k(z(i))$ for the $k$-th guard after $i$ iterations from the initial value $z$. Expanding the powers of the blocks, $\mathrm{Cond}_k(z(i))$ is a sum over indices $\mathit{ind} = (l, j)$ of terms $\binom{i}{j-1} \lambda_l^{\,i-(j-1)}\, C_{k,\mathit{ind}}\, z$, where $C_{k,\mathit{ind}}$ collects the coefficients of that term; the indices are ordered so that terms with larger indices grow faster as $i$ increases, and $\Pi_2(l, j) = j$. The nondeterministic procedure that guesses for each guard $k$ a dominant index $\mathit{index}(k)$, and returns "nonterminating" exactly when the linear system

$$C_{k,\mathit{ind}}\, z = 0 \ \text{for } \mathit{ind} \succ \mathit{index}(k), \qquad C_{k,\mathit{index}(k)}\, z > 0, \qquad \mathrm{Cond}_k(z(i)) > 0 \ \text{for } 0 \le i \le \Pi_2(\mathit{index}(k))$$

is satisfiable over $\mathbb{R}$ for some guess, returns "nonterminating" if and only if $P_4$ does not terminate on some real input.

## Expansion

This page becomes ready once these prerequisites are stated and checked:

- The closed form of the powers of a Jordan block and the growth order on the indices $(l, j)$ (statement prerequisite)
- A proof of correctness of the procedure, which the source states without proof (source check)

## Depends on

- [Restriction to positive-eigenvalue blocks](restriction-to-positive-eigenvalue-blocks.md)

## Sources

- A. Tiwari, "Termination of linear programs", *Computer Aided Verification (CAV 2004)*, LNCS 3114, Springer, 2004, pp. 70–82, author copy <https://www.csl.sri.com/users/tiwari/papers/cav04.pdf>, Section 4, the three-step nondeterministic algorithm and Lemma 2 (stated without proof).
