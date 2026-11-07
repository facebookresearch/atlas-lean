# Touchard's Catalan identity

For every natural number $n$, writing
$C_k = \binom{2k}{k}/(k+1)$ for the $k$-th Catalan number,

$$C_{n+1} = \sum_{i=0}^{\lfloor n/2 \rfloor} \binom{n}{2i} 2^{n-2i} C_i.$$

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL20/Dershowitz/dersh3.tex, lines 274-277. Grounded record `jis_grounded_8d6801e19f84ccd671cecd8e`, concept `jis_dep_66a308b917e737cb196c1412`. File SHA-256 `f34deece6b6101298cf0abee4c3e12577a8a7db55afe76325aef6447839e0646`, exact span SHA-256 `ba2f60f14652718c971cd41bf7b6a3f069a5e835bad930bd72a403a07d400f25`. A second JIS source prints the finite upper bound as `floor(n/2)`.
