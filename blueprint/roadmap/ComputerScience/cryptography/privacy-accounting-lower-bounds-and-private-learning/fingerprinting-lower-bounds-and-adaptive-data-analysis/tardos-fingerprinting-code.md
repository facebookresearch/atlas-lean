# Tardos codes: optimal fully collusion-resilient fingerprinting

For $c \ge 4$ there are fingerprinting codes for $N$ users, secure against coalitions of up to $c$ users with error at most $\xi$ (some innocent user is accused with probability at most $\xi$, and the coalition escapes tracing with probability at most $\xi$), of length $m = 100c^2 \lceil \log(N/\xi) \rceil = O(c^2 \log(N/\xi))$. The code is Tardos's code with per-user error $\xi/N$, that is, with $k = \lceil \log(N/\xi) \rceil$: draw biases $p_1, \dots, p_m$ independently from the arcsine-type density proportional to $1/\sqrt{p(1-p)}$ on $[t, 1-t]$ with $t = 1/(300c)$, and give user $i$ the codeword $x_i \in \{0,1\}^m$ with independent bits $\Pr[x_{ij} = 1] = p_j$. Let $U_{ij} = \sqrt{(1-p_j)/p_j}$ if $x_{ij} = 1$ and $U_{ij} = -\sqrt{p_j/(1-p_j)}$ if $x_{ij} = 0$. Given a pirated word $y \in \{0,1\}^m$, accuse user $i$ when the score $S_i = \sum_j y_j U_{ij}$ exceeds $Z = 20c\lceil \log(N/\xi) \rceil$; a column with $y_j = 0$ contributes $0$. For fully collusion-resilient codes ($c = N = n \ge 4$) this length is $O(n^2 \log(n/\xi))$.

Conversely, fix $a > 1$ and let $3 \le c \le N$. If a fingerprinting code for $N$ users and coalitions of size up to $c$ has error $\xi < 1/(100c^a)$ in both senses, that is, every fixed innocent user is accused with probability at most $\xi$ and a coalition escapes tracing (no member is accused) with probability at most $\xi$, then its length is $\Omega(c^2\log(1/\xi))$. Hence, in this regime of coalition size and small error, and when $\log(N/\xi) = O(\log(1/\xi))$, the construction above has optimal length up to a constant factor. The lower bound is not uniform outside this regime: for a single pirate, distinct identifiers of length $\lceil\log_2 N\rceil$ trace with zero error.

## Proof sketch

Under the marking assumption the pirate's word agrees with the coalition wherever all coalition members agree. Soundness and tracing are separate tail bounds. For an innocent user $i$, the weights $U_{ij}$ are independent of $y$ and have mean zero given $p_j$, so an exponential-moment bound shows that $S_i$ exceeds $Z$ with probability at most $\xi/N$, and a union bound covers all innocent users. For tracing, Tardos bounds the lower tail of the coalition's total score $\sum_{i \in C} S_i$: against any pirate strategy obeying the marking assumption, it is at most $cZ = 20c^2\lceil \log(N/\xi) \rceil$ only with probability at most $(\xi/N)^{c/4} \le \xi^{c/4}$, which is at most $\xi$ because $c \ge 4$, using the bias distribution to make every column with $y_j = 1$ contribute positively in expectation (Tardos, Section 2.1). On the complementary event the total exceeds $cZ$; since the coalition has at most $c$ members, some member has score strictly greater than $Z$, and the strict accusation rule accuses it. A score equal to $Z$ is not an accusation, which is why the lower-tail event is taken with $\le cZ$. The lower bound uses a symmetric strategy for the coalition and an information-theoretic argument.

## Depends on

- [Fingerprinting codes](../../differential-privacy/fingerprinting-codes.md)
- [Tardos score](../../differential-privacy/tardos-score.md)
- [Tardos accusation](../../differential-privacy/tardos-accuses.md)

## Sources

- G. Tardos, "Optimal Probabilistic Fingerprint Codes", STOC (2003); Journal of the ACM 55 (2008), author's copy, Section 2.1 (the code $F_{n,c,\varepsilon}$), Theorems 1 and 2, Corollary 3 (the code $F_{n,c,\varepsilon/n}$ is $\varepsilon$-secure against coalitions of size $c$ if $c \ge 4$) and Theorem 4 (the lower bound).
- D. Boneh, J. Shaw, "Collusion-Secure Fingerprinting for Digital Data", CRYPTO (1995); IEEE Transactions on Information Theory 44 (1998).
