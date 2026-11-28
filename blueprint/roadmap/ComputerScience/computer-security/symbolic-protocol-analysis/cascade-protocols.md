# Cascade protocols

Each user $A$ has a public encryption operator $E_A$ and a private decryption operator $D_A$ with $E_A D_A = D_A E_A = 1$. A word over these operators *reduces* by deleting
factors $E_A D_A$ and $D_A E_A$ until none is left, giving its unique reduced form; $\mathrm{It}(\gamma)$ is the set of operators occurring in $\gamma$. A *two-party cascade
protocol* $T$ is given by words $\bar\alpha_1, \dots, \bar\alpha_t$ and $\bar\beta_1, \dots, \bar\beta_{t'}$ ($t' \in \{t, t - 1\}$) over placeholders for $E_X, E_Y, D_X$ (for the $\bar\alpha_i$) and $E_X, E_Y, D_Y$ (for the
$\bar\beta_j$); substituting users $A, B$ gives $\alpha_i(A, B)$ and $\beta_j(A, B)$, assumed reduced. To send a plaintext $M$ to $Y$, $X$ sends $N_1(X, Y) M$ with $N_1 = \alpha_1(X, Y)$, and the
parties alternately apply their words: $N_{2j} = \beta_j(X, Y) N_{2j-1}$ and $N_{2i+1} = \alpha_{i+1}(X, Y) N_{2i}$.

For a third user $Z$, let $\Sigma_1(Z)$ be all encryption operators together with $D_Z$, $\Sigma_2 = \{\alpha_i(A, B) \mid A \ne B,\ i \ge 2\}$ and $\Sigma_3 = \{\beta_i(A, B) \mid A \ne B,\ i \ge 1\}$: what
the saboteur $Z$ can apply itself or get honest users to apply. $T$ is *insecure* if some word $\gamma$ over $\Sigma_1(Z) \cup \Sigma_2 \cup \Sigma_3$ has $\gamma N_i(X, Y)$ reducing to the empty word for
some $i$, so that $Z$ recovers $M$; otherwise $T$ is *secure*. These definitions use only words over unary operators modulo cancellation; the later
Dolev–Yao deduction systems with pairing and symmetric encryption generalize the setting but are not needed here.

## Sources

- D. Dolev and A. C. Yao, "On the security of public key protocols", *IEEE Transactions on Information Theory* 29(2):198–208, 1983, copy at <https://www.cs.huji.ac.il/~dolev/pubs/dolev-yao-ieee-01056650.pdf>: Section II-A (operators and reduction) and Section II-B, Definitions 1–3.
