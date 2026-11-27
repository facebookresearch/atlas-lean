# Layer representation and enumeration of multistate nested canalizing functions

**Setting.** Let $\mathbb{F}_p=\{0,1,\dots,p-1\}$ with its natural order, $p$ prime. A proper subset $S\subsetneq\mathbb{F}_p$ is an *interval* if $S=\{0,\dots,j\}$ or $S^c=\{0,\dots,j\}$ for some $0\le j<p-1$, so there are $2(p-1)$ intervals. Fix a permutation $\sigma$ of $\{1,\dots,n\}$, intervals $S_1,\dots,S_n$, and outputs $b_1,\dots,b_{n+1}\in\mathbb{F}_p$ with $b_n\ne b_{n+1}$. A function $f:\mathbb{F}_p^n\to\mathbb{F}_p$ is **nested canalizing** (NCF) in the order $x_{\sigma(1)},\dots,x_{\sigma(n)}$ if

$$f(x)=b_k\quad\text{when } x_{\sigma(1)}\notin S_1,\dots,x_{\sigma(k-1)}\notin S_{k-1},\ x_{\sigma(k)}\in S_k\qquad(1\le k\le n),$$

and $f(x)=b_{n+1}$ when $x_{\sigma(j)}\notin S_j$ for all $j$. Such functions are the multistate analogue of the nested canalizing Boolean rules found in published gene regulatory network models. Let $Q_S(x)=0$ for $x\in S$ and $Q_S(x)=1$ for $x\in S^c$.

**Theorem (layer representation).** For $n\ge2$, $f$ is nested canalizing iff it can be written uniquely as

$$f=M_1\Big(M_2\big(\cdots\big(M_{r-1}(B_{r+1}M_r+B_r)+B_{r-1}\big)\cdots\big)+B_2\Big)+B_1,$$

where $M_i=\prod_{j=1}^{k_i}Q_{S_{i_j}}(x_{i_j})$ are products of indicators over disjoint variable sets that partition $\{1,\dots,n\}$ ($k_i\ge1$, $k_1+\cdots+k_r=n$), $B_1\in\mathbb{F}_p$, $B_2,\dots,B_{r+1}\ne0$, and $B_{r+1}+B_r\ne0$ whenever $k_r=1$. The *layer number* $r$ is therefore an invariant of $f$. Variables can be reordered only within a layer, and $r$ can be read off the canalized outputs $\beta=(b_1,\dots,b_{n+1})$ as the number of maximal constant blocks of $(b_1,\dots,b_n)$.

**Corollary (closed-form count).** For $n\ge2$ the number of NCFs over $\mathbb{F}_p$ in $n$ variables is

$$|\mathrm{NCF}(n)|=2^{n-1}p(p-2)\sum_{r=2}^{n}(p-1)^{n+r-1}\!\!\sum_{\substack{k_1+\cdots+k_{r-1}=n-1\\k_i\ge1}}\!\!\binom{n}{k_1,\dots,k_{r-1}}+2^np\sum_{r=1}^{n-1}(p-1)^{n+r}\!\!\sum_{\substack{k_1+\cdots+k_r=n\\k_i\ge1,\ k_r\ge2}}\!\!\binom{n}{k_1,\dots,k_r}.$$

For $p=2$ this reduces to the Boolean counts $8,64,736$ for $n=2,3,4$. For $p=3$ it gives $192,5568,219648$, and for $p=5$ it gives $5120,547840,78561280$. It also solves in closed form the nonlinear recursion $a_2=4(p-1)^4$, $a_n=\sum_{r=2}^{n-1}\binom{n}{r-1}2^{r-1}(p-1)^ra_{n-r+1}+2^{n-1}(p-1)^{n+1}(2+n(p-2))$, via $|\mathrm{NCF}(n)|=p\,a_n$.

**Generalization and permutation classes.** Over any finite field $\mathbb{F}_q$, allow the canalizing input sets to be arbitrary proper subsets. The same unique layer representation holds, and the count is obtained by replacing $p\to q$ and the $2(p-1)$ intervals by the $2^q-2$ proper subsets. Call two functions permutation equivalent if they differ by a permutation of the variables. The number of permutation-equivalence classes of generalized NCFs in $n$ variables is

The formula $N = 2^{n-1}(q-1)q^n(2^{q-1}-1)^n$ of Theorem 4.2 counts nested canalizing functions with a *fixed* variable order, not permutation equivalence classes (which are strictly fewer — e.g., 6 rather than 8 for $q=2, n=2$; Theorem 4.2 of arXiv:1304.3707 erroneously states this as the number of permutation classes).

## Expansion

Set $b_i=B_1+\cdots+B_i$. Expanding the nested form shows that the variables of $M_1$ canalize to $B_1$. When all of them are non-canalizing, the variables of $M_2$ canalize to $B_1+B_2\ne B_1$, and so on. Conversely, grouping consecutive equal canalized outputs of an NCF into blocks gives the layers. Uniqueness holds because a variable canalizes $f$ only if it lies in the first layer: deeper variables canalize only subfunctions, and those have different outputs. The condition $B_{r+1}+B_r\ne0$ when $k_r=1$ excludes $bQ_S+a$ with $a=-b$, which equals $-bQ_{S^c}$ and would collapse to $r-1$ layers. Of the functions $bQ_S+a$ with $a,b\ne0$, exactly $(p-1)^2(p-2)$ are not of the form $cQ_{S'}$. For $k\ge2$, the $2^k(p-1)^{k+2}$ functions $b\prod_jQ_{S_j}(x_j)+a$ with $a,b\ne0$ are all distinct. Counting choices layer by layer, with multinomial coefficients for assigning variables to layers, gives the corollary. Dropping the multinomial factor, that is, fixing the variable order, counts permutation classes; the identity $\sum_{k_1+\cdots+k_r=n,\ k_i\ge s_i}1=\binom{r+n-s-1}{r-1}$ then collapses the sums into the closed form.

## Sources

- Claus Kadelka, Yuan Li, Jack Kuipers, John O. Adeyeye and Reinhard Laubenbacher, "Multistate nested canalizing functions and their networks", Theoretical Computer Science 675 (2017), 1–14, <https://doi.org/10.1016/j.tcs.2017.01.031>; numbering as in arXiv:1304.3707: Section 2 (definition of multistate NCF), Theorem 3.1 with the layer-number definition and the counting corollaries of Section 3, and Theorem 4.1 and Theorem 4.2 with the generalized counting corollary of Section 4. The paper prints $219468$ for $p=3$, $n=4$; evaluating its closed-form formula gives $219648$.
