# Barrett reduction estimates the quotient within two

Barrett reduction replaces division by a $k$-digit modulus $m$ with multiplication by the precomputed constant $\mu=\lfloor b^{2k}/m\rfloor$. The quotient estimate is never too large and at most two too small, so at most two subtractions of $m$ finish the reduction.

Let the radix be an integer $b>3$ and let $k\ge 1$. Let $m$ be a positive integer with exactly $k$ base-$b$ digits, $b^{k-1}\le m<b^{k}$, and let $x$ be a positive integer with at most $2k$ base-$b$ digits, $x<b^{2k}$. Put $\mu=\lfloor b^{2k}/m\rfloor$, write $x=Qm+R$ with $0\le R<m$, and set

$$
q_1=\Bigl\lfloor\frac{x}{b^{k-1}}\Bigr\rfloor,\qquad q_3=\Bigl\lfloor\frac{q_1\mu}{b^{k+1}}\Bigr\rfloor .
$$

Then $Q-2\le q_3\le Q$. Hence $0\le x-q_3m=(Q-q_3)m+R<3m<b^{k+1}$, so $x-q_3m$ is determined by $x\bmod b^{k+1}$ and $q_3m\bmod b^{k+1}$, and $x\bmod m$ follows from it by at most two subtractions of $m$ (Barrett's algorithm, HAC Algorithm 14.42).

## Depends on

None.

## Proof depends on

None.

## Expansion

HAC justifies the estimate by writing $Q=\lfloor (x/b^{k-1})(b^{2k}/m)(1/b^{k+1})\rfloor$ and approximating each factor from below by its floor: $q_3$ never exceeds the true quotient and is at most $2$ smaller (Fact 14.43, Note 14.44(i)). Note 14.44(ii) then uses $3m<b^{k+1}$, which holds since $m<b^{k}$ and $b>3$, to recover $x-q_3m$ from residues modulo $b^{k+1}$ and to bound the final loop by two subtractions. The trivial input $x=0$ gives $q_3=Q=0$.

## Sources

- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied Cryptography*, CRC Press (1996), Chapter 14, §14.3.3: Algorithm 14.42 (Barrett modular reduction, with the standing assumption $b>3$), Fact 14.43 and Note 14.44; chapter copy distributed with the publisher's permission at [cacr.uwaterloo.ca/hac](https://cacr.uwaterloo.ca/hac/about/chap14.pdf).
