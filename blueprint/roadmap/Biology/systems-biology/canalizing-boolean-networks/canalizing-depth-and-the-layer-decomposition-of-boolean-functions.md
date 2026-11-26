# Canalizing depth and the layer decomposition of Boolean functions

Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean function, with arithmetic over $\mathbb{F}_2$ (product = AND, sum = XOR). A nonconstant $f$ is **canalizing in $x_i$** with canalizing value $a \in \{0,1\}$ if $f(x_1,\dots,x_{i-1},a,x_{i+1},\dots,x_n)$ is constant. The function $f$ has **canalizing depth $k$** if it can be written as a nested rule

$$f(x) = \begin{cases} b_1, & x_{i_1} = a_1,\\ b_2, & x_{i_1} \neq a_1,\ x_{i_2} = a_2,\\ \ \vdots & \\ b_k, & x_{i_1} \neq a_1,\dots,x_{i_{k-1}} \neq a_{k-1},\ x_{i_k} = a_k,\\ g(x), & x_{i_1} \neq a_1,\dots,x_{i_k} \neq a_k, \end{cases}$$

with distinct indices $i_1,\dots,i_k$, bits $a_j, b_j$, $g \not\equiv b_k$, and the **core** $g$ a noncanalizing function of the remaining variables. Because the core is required to be noncanalizing, every function has a single well-defined depth: noncanalizing functions have depth $0$, and **nested canalizing** functions have the maximal depth $n$ (constant core). A Boolean network $(f_1,\dots,f_n)$ has canalizing depth $k$ when each $f_i$ has depth $k$.

**Layer decomposition (He–Macaulay).** Every Boolean function $f \not\equiv 0$ can be written uniquely as

$$f = M_1\Bigl(M_2\bigl(\cdots\bigl(M_{r-1}(M_r\,p_C + 1) + 1\bigr)\cdots\bigr) + 1\Bigr) + b, \qquad M_i = \prod_{j=1}^{k_i} (x_{i_j} + a_{i_j}),$$

where $p_C \not\equiv 0$ is noncanalizing, each variable occurs in exactly one of $M_1,\dots,M_r,p_C$, and $k = k_1 + \dots + k_r$ is the canalizing depth of $f$. The only restrictions are two exceptional cases: (E1) if $p_C \equiv 1$ and $r \neq 1$ then $k_r \geq 2$; (E2) if $p_C \equiv 1$, $r = 1$ and $k_1 = 1$ then $b = 0$.

Consequently a uniformly random function of fixed depth $k$ in $n$ variables can be sampled by drawing the bits $b, a_1,\dots,a_n$, a random $k$-subset of variables, a uniformly random ordered partition of it into layers $X_1 \sqcup \dots \sqcup X_r$, and a random noncanalizing core on the other variables, then rejecting outputs that violate (E1)–(E2); this takes $O(n\,2^n)$ time, nearly optimal for an output of size $2^n$.

## Expansion

Each layer $M_i$ is a product of literals: if any literal in $M_1$ vanishes (some $x_{i_j} = a_{i_j}$), the whole expression collapses to $b$, which is the first canalizing step; if all literals of $M_1$ equal $1$, the value is $M_2(\cdots)+1+b$ and the next layer acts with the complemented output. Variables inside one layer canalize with the same output, so they form an unordered block, while blocks are ordered; this is why sampling needs a uniform *ordered* set partition, counted by the Fubini recurrence $p_j = \sum_{i=0}^{j-1} \binom{j}{i} p_{j-i}$, $p_0 = 1$. Uniqueness of the decomposition makes the sampler uniform. The exceptional cases remove the two ambiguities that appear when the core is constant (a last layer of size one can be merged into the constant). Noncanalizing cores are found by rejection, which is fast because canalizing functions are a vanishing fraction of all Boolean functions.

## Sources

- E. Paul, G. Pogudin, W. Qin, R. Laubenbacher, "The dynamics of canalizing Boolean networks", *Complexity* 2020 (2020) 3687961. Definitions 3–6, Theorem 1 (citing He and Macaulay, Theorem 4.5), Algorithms 2–3, Remarks 2–3. <https://doi.org/10.1155/2020/3687961>. PMCID: PMC10399297.
