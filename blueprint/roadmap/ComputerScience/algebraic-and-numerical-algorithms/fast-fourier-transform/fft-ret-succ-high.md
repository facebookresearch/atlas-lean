# High half of the FFT butterfly recurrence

Let $R$ be a commutative ring, $d$ a natural
number, $\omega \in R$ and $x \in R^{2^{d+1}}$, with entries indexed from $0$. Let
$e, o \in R^{2^d}$ be the even- and odd-indexed subsequences of $x$ returned by the FFT split,
and let $E$ and $O$ be the vectors returned by the radix-two FFT of depth $d$ with root
$\omega \cdot \omega$ on $e$ and on $o$. Then for every $k < 2^d$, entry $k + 2^d$ of the
vector returned by the radix-two FFT of depth $d + 1$ with root $\omega$ on $x$ equals
$E_k - \omega^k O_k$.
