# Brown measure of the block-product weighted shift

Use the comparator's [recursively selected blocks](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ProductBrown.lean#L195-L288) $I=\coprod_{s\ge0}\{0,\ldots,m_s-1\}$, cutoff $K_s$ and block costs $c_i=C_s=\max(L_s,K_s^2)$ for $i$ in block $s$. Selection is fixed by the comparator's classical choice from existence of a stage choice at each recursively computed state; the statement here is not quantified over alternative stage selections. The stage state $(K,G,d,B,L_{\rm prev})$ starts at $(100,1,0,0,1)$. At stage $s$ select $(\epsilon,L,G',m)$ subject to the polynomial lower bound specified below, $\epsilon>0$, $L\ge L_{\rm prev}$, $3(2K+1)e^{-L/10000}\le\epsilon/(s+1)$, $G'\ge1$, $\kappa_{s+1}\sqrt{G'}\ge L$ for $\kappa_s=1/(100(s+1))$, $m\ge\max(K,2^{s+1},4G,100,100d)$, $\kappa_s m^{1/40}\ge L$, and $G'\lceil m^{3m/4}\rceil<m^{4m/5}$. The next state is $(\lceil m^{3m/4}\rceil,G',d+m,B+C_s m,L)$. The polynomial lower bound means that for any two complex coefficient vectors of length $2K+1$, entries bounded by $e^{(K+1)B}$ and middle coefficient of modulus at least $1/(s+1)$ in each, one of the first $2K+1$ coefficients of their polynomial product has modulus at least $\epsilon$.

For every assignment $1/(m_s K_s)\le\theta_i\le2/(m_s K_s)$ for $i$ in block $s$, take $H=L^2([0,1)^I\times\mathbb Z)$ with product probability on the first factor and counting measure on the second. Define $D$ by multiplication by $\exp(-\sum_i c_i\lfloor\{x_i+k\theta_i\}+\theta_i\rfloor)$ at $(x,k)$, using the real sum convention of the comparator (zero if the real sum is not summable). Take $T=UD$ where $U$ shifts $k$ to $k-1$ in its argument. Let $e(x,k)=\mathbf1_{k=0}$ and $\tau(S)=\langle e,Se\rangle$. With $\ell_n(t)=\log(\max(e^{-n},t))$ and $|A|=(A^*A)^{1/2}$, the conclusion is that $\delta_0$ is a compactly supported probability measure with the determinant identity, for every $z\in\mathbb C$,

$$\inf_{n\ge0}\exp(\operatorname{Re}\tau(\ell_n(|T-zI|)))=\inf_{n\ge0}\exp\left(\int\ell_n(|z-w|)\,d\delta_0(w)\right).$$

No rational-independence claim is added to this quantification over the prescribed angle intervals.

## Depends on

- The recursively selected block stages, the product multiplier and shift, and the cutoff determinant identity above.

## Proof depends on

- The scale and coefficient-product estimates for the chosen blocks, and the control of the cutoff determinants of all scalar translates of their weighted shift.

## Expansion

Separate existence of stage choices from the measurable product multiplication operator and trace vector. Derive the translated determinant formula for every allowed angle assignment, including zero scalar translate, and only then compare with the point-mass potential. This is not the Brown claim for a freely chosen product rotation with additional ergodicity hypotheses.

## Sources

- OpenAI, [ProductBrown comparator, productBrown](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ProductBrown.lean#L751-L754).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/293.md).
