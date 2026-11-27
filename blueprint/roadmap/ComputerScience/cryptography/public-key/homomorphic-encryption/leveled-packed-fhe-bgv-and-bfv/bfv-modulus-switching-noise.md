# Invariant-noise identity for BFV modulus switching

Switching a two-component BFV ciphertext from modulus $q$ down to $p$ by half-up rounding of $\tfrac pq c_i$ shifts its invariant-noise coset by exactly $\tfrac tp(\tau_0+\tau_1s)$, where $\tau_0,\tau_1$ are the rounding errors.

Let $2\le p<q$, let $t\ge 2$, and let $\mathrm{ct}=(c_0,c_1)$ be a BFV ciphertext modulo $q$ encrypting $m\in R_t$ under the secret $s\in R=\mathbb{Z}[x]/(x^n+1)$. Take the centered representatives $c_0,c_1\in R$, with coefficients in $[-q/2,q/2)$, and let $v\in\mathbb{Q}[x]/(x^n+1)$ be an element of the invariant-noise coset of $\mathrm{ct}$, so $\tfrac tq(c_0+c_1s)=m+v+at$ for some $a\in R$. Define the switched ciphertext by $c_i'=\lfloor\tfrac pq c_i\rceil$ with the coefficientwise rounding $\lfloor z\rceil=\lfloor z+\tfrac12\rfloor$, put $\tau_i=c_i'-\tfrac pq c_i$ (coefficients in $(-\tfrac12,\tfrac12]$), and let $\mathrm{ct}'=([c_0']_p,[c_1']_p)$. Then

$$
\frac{t}{p}\bigl(c_0'+c_1's\bigr)=m+v+\frac{t}{p}\bigl(\tau_0+\tau_1s\bigr)+at .
$$

Hence $v+\tfrac tp(\tau_0+\tau_1s)$ lies in the invariant-noise coset of $\mathrm{ct}'$ with respect to $p$, and the invariant noise of $\mathrm{ct}'$ has infinity norm at most that of this element. The element need not be the minimal representative. Decryption of $\mathrm{ct}'$ is correct if its invariant noise has infinity norm below $1/2$, a sufficient condition that the identity alone does not ensure.

## Depends on

- [Invariant noise of a BFV ciphertext](bfv-invariant-noise.md)

## Proof depends on

None.

## Expansion

Costache, Laine and Player obtain the identity by substituting $c_i'=\tfrac pq c_i+\tau_i$: $\tfrac tp(c_0'+c_1's)=\tfrac tq(c_0+c_1s)+\tfrac tp(\tau_0+\tau_1s)$. Reducing $c_i'$ modulo $p$ changes the left side only by an element of $tR$. Fixing the centered input lifts and a translation-invariant rounding makes $\mathrm{ct}'$ a well-defined function of $\mathrm{ct}$.

## Sources

- Anamaria Costache, Kim Laine, Rachel Player, "Evaluating the Effectiveness of Heuristic Worst-Case Noise Analysis in FHE", Computer Security – ESORICS 2020, Lecture Notes in Computer Science, Springer (2020), DOI [10.1007/978-3-030-59013-0_27](https://doi.org/10.1007/978-3-030-59013-0_27): §4.1, the ModSwitch statement for FV and its proof (identity $v_{\mathrm{mod}}=v+\tfrac tp(\tau_0+\tau_1s)$); authors' repository copy of IACR ePrint 2019/493.
