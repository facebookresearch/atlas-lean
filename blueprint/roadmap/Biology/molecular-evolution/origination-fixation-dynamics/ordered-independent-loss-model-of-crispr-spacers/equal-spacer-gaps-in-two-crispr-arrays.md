# Distribution of shared-spacer positions in two CRISPR arrays under the ordered independent loss model

**Model (ordered independent loss model).** A CRISPR array is a sequence $s=(s_1,s_2,\dots)\in[0,1]^{\mathbb N}$ of spacer labels, with $s_1$ at the leader end. Along a lineage the array evolves as a Markov jump process: at rate $\theta>0$ a new spacer with an independent uniform label $U\in[0,1]$ is inserted at the leader end, $s\mapsto(U,s_1,s_2,\dots)$; independently, each present spacer $s_i$ is deleted at rate $\rho>0$, $s\mapsto(s_1,\dots,s_{i-1},s_{i+1},\dots)$. The law $\pi$ of an i.i.d. uniform sequence is an equilibrium of this process. Along a rooted ultrametric tree, the process starts from $\pi$ at the root and evolves independently along the descending branches.

**Statement.** Take two leaves $1,2$ at distance $d(1,2)=2T$ ($T\ge 0$ is the time to their most recent common ancestor). Let $V_i$ (resp. $W_i$) be the position, counted from $1$ at the leader end, in array $1$ (resp. $2$) of the $i$-th spacer of that array that is also present in the other array, with $V_0=W_0=0$. Let $(A,B),(A_1,B_1),(A_2,B_2),\dots$ be i.i.d. with

$$
\mathbb P(A=a,B=b)=\binom{a+b}{a}\,\frac{e^{-\rho T}}{2-e^{-\rho T}}\left(\frac{1-e^{-\rho T}}{2-e^{-\rho T}}\right)^{a+b},\qquad a,b\in\{0,1,2,\dots\},
$$

and let $C_1,C_2$ be i.i.d. Poisson with mean $\frac{\theta}{\rho}(1-e^{-\rho T})$, independent of the pairs. Then the increments

$$
(V_1,W_1),\ (V_2-V_1,W_2-W_1),\ (V_3-V_2,W_3-W_2),\dots
$$

are independent, with $(V_1-1,W_1-1)\sim(C_1+A_1,\,C_2+B_1)$ and $(V_i-V_{i-1}-1,\,W_i-W_{i-1}-1)\sim(A_i,B_i)$ for $i\ge 2$.

In particular, with $p=e^{-\rho T}$, each of $A$ and $B$ is geometric on $\{0,1,\dots\}$ with success probability $p$, $\mathbb P(A=a)=p(1-p)^a$; so each marginal gap $V_i-V_{i-1}$ ($i\ge 2$) is geometric on $\{1,2,\dots\}$ with success probability $p$, and the gaps between consecutive shared spacers do not depend on the insertion rate $\theta$.

## Expansion

Spacers already present at the common ancestor are the only ones that can be shared, since new insertions on the two branches carry a.s. distinct labels. An ancestral spacer survives on one branch of length $T$ with probability $p=e^{-\rho T}$, independently on the two branches and across spacers. Scanning the ancestral array from the leader end, each ancestral spacer is independently "kept in both" (probability $p^2$), "kept only in 1" or "only in 2" (probability $p(1-p)$ each), or lost in both. Between two consecutive shared spacers, the numbers $A_i$ and $B_i$ of spacers kept only in $1$ and only in $2$ therefore follow a negative-multinomial-type law: conditioning on not being lost in both gives success probability $p^2/(1-(1-p)^2)=p/(2-p)$ and probability $(1-p)/(2-p)$ for each of the two one-sided outcomes, which yields the binomial-coefficient formula; summing it over $b$ gives $\mathbb P(A=a)=p(1-p)^a$. The gap $V_i-V_{i-1}$ is $A_i$ plus one, the step onto the $i$-th shared spacer itself. Before the first shared spacer, array $\ell$ also carries the spacers inserted on its own branch since the split that are still present; by the death–immigration dynamics this count is Poisson with mean $\frac{\theta}{\rho}(1-e^{-\rho T})$, and it is independent of the ancestral pattern, so $V_1-1=C_1+A_1$ and $W_1-1=C_2+B_1$.

## Sources

- Franz Baumdicker, Ariana M. I. Huebner and Peter Pfaffelhuber, *The independent loss model with ordered insertions for the evolution of CRISPR spacers*, Theor. Popul. Biol. 119 (2018), 72–82. <https://doi.org/10.1016/j.tpb.2017.11.001> Definition 2.1 and Definition 2.5 (the model), Lemma 2.2 (equilibrium), Definition 2.7 (equal spacers), Theorem 1 (two-leaf distribution), Remarks 3.1 and 3.3 (geometric gaps). Locators use the numbering of the preprint arXiv:1703.00220. Theorem 1 there states the increments without the shift by one that positions starting at $1$ require; its proof counts the spacers before each shared one, which is the shifted form stated here.
