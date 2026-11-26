# Tardos codes: optimal fully collusion-resilient fingerprinting

There are fingerprinting codes for $N$ users, secure against coalitions of up to $c$ users with false-accusation probability at most $\xi$, of length $m = O(c^2 \log(N/\xi))$: draw biases $p_1, \dots, p_m$ independently from the arcsine-type density proportional to $1/\sqrt{p(1-p)}$ on $[t, 1-t]$ with $t \approx 1/(300c)$, give user $i$ the codeword $x_i \in \{0,1\}^m$ with independent bits $\Pr[x_{ij} = 1] = p_j$, and accuse user $i$ when the correlation score $\sum_j \big(\text{sign-adjusted } \sqrt{(1-p_j)/p_j}\text{ or } -\sqrt{p_j/(1-p_j)}\big)$ of $x_i$ with a pirated word exceeds a threshold of order $c\log(N/\xi)$. For fully collusion-resilient codes ($c = N = n$) this length is $O(n^2 \log(n/\xi))$.

Conversely, fix $a > 1$ and let $3 \le c \le N$. If a fingerprinting code for $N$ users and coalitions of size up to $c$ has error $\xi < 1/(100c^a)$ in both senses, that is, every fixed innocent user is accused with probability at most $\xi$ and a coalition escapes tracing (no member is accused) with probability at most $\xi$, then its length is $\Omega(c^2\log(1/\xi))$. Hence, in this regime of coalition size and small error, and when $\log(N/\xi) = O(\log(1/\xi))$, the construction above has optimal length up to a constant factor. The lower bound is not uniform outside this regime: for a single pirate, distinct identifiers of length $\lceil\log_2 N\rceil$ trace with zero error.

## Proof sketch

Under the marking assumption the pirate's word agrees with the coalition wherever all coalition members agree. The scoring rule is designed so that the coalition's total score has expectation of order $m/c$ against any pirate strategy (using the bias distribution to make each column informative), so some member's score exceeds the threshold, while an innocent user's score is a sum of independent mean-zero bounded terms and exceeds the threshold with probability at most $\xi/N$ by a Bernstein bound. The lower bound uses a symmetric strategy for the coalition and an information-theoretic argument.

## Depends on

- [Fingerprinting codes](../../differential-privacy/fingerprinting-codes.md)

## Sources

- G. Tardos, "Optimal Probabilistic Fingerprint Codes", STOC (2003); Journal of the ACM 55 (2008).
- D. Boneh, J. Shaw, "Collusion-Secure Fingerprinting for Digital Data", CRYPTO (1995); IEEE Transactions on Information Theory 44 (1998).
