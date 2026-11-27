# Finding hard tautologies is computationally hard

Certifying that a small nondeterministic circuit does not accept exactly the tautologies of a given size cannot be done in time $2^{O(k)}$ if exponentially hard one-way permutations exist; under a stronger Nisan-Wigderson hypothesis such certificates sometimes do not exist.

For a constant $c \ge 1$ the search task $\mathbf{Cert}(c)$ is: given $1^{(k)}$ and a size $k^{c^2}$ circuit $D(x, y)$ with $k$ inputs $x$ and $\ell = k^c$ inputs $y$, output either a size-$k$ falsifiable formula $\varphi$ with $D(\varphi, y)$ satisfiable, or a size-$k$ tautology $\tau$ with $D(\tau, y)$ unsatisfiable. The output certifies that $D$, read as a nondeterministic circuit, does not accept $\mathrm{TAUT} \cap \{0,1\}^k$: either $D$ is not sound as a proof system restricted to size-$k$ formulas and size-$\ell$ proofs, or it has a lower bound witnessed by $\tau$. For a proof system $P$ and constants $c_1 \ge c_0 \ge 1$, the promise task $\mathbf{Find}(P, c_1, c_0)$ is: given $1^{(k)}$ and a tautology $\alpha$ with $|\alpha| \le k^{c_0}$, output a size-$k$ tautology $\beta$ without a proof of size less than $k^{c_1}$ in $P + \alpha$ ($P$ with $\alpha$ as an extra axiom scheme).

**Theorem.** Assume that an exponentially hard one-way permutation exists: a polynomial-time, length-preserving permutation $h$ of $\{0,1\}^*$ and a constant $\delta > 0$ such that for every $\ell$ and every circuit $D$ with $\ell$ inputs and size at most $2^{\ell^\delta}$, $\Pr_{v \in \{0,1\}^\ell}[D(h(v)) = v] \le 2^{-\ell^\delta}$. Then there is $c \ge 1$ such that no deterministic time-$2^{O(k)}$ algorithm solves $\mathbf{Cert}(c)$ on all lengths $k \ge 1$. This hypothesis measures security against circuits of size $2^{\ell^\delta}$; it differs from the security against uniform polynomial-time inverters with negligible success in the general notion of a one-way permutation.

If moreover a conjecture on the proof complexity of Nisan-Wigderson generators holds (Part 3 of Statement (S) of the author's earlier work), then for every decent Cook-Reckhow proof system $P$ there are constants $c_1 \ge c_0 \ge 1$ such that $\mathbf{Find}(P, c_1, c_0)$, with proof-size exponent $c_1$ and axiom-size exponent $c_0$, has no solution for infinitely many lengths $k$.

Here a proof system $P$ is **decent** if polynomial-time algorithms perform the following tasks, where $\mathrm{Sat}_k(u, x, v)$ are fixed formulas of size $k^{O(1)}$, with $|u| = |x| = k$, such that for all $a, \varphi \in \{0,1\}^k$, $\mathrm{Sat}_k(a, \varphi, v)$ is a tautology iff $a$ is a truth assignment satisfying the formula $\varphi$: (D1) from a $P$-proof of $\psi(x)$ and a truth assignment $a$ to $x$, construct a $P$-proof of $\psi(a)$; (D2) given a true sentence $\psi$ without variables, construct a $P$-proof of it; (D3) from $P$-proofs of $\psi$ and of $\psi \to \eta$, construct a $P$-proof of $\eta$; (D4) given a formula $\varphi(u)$ and a $P$-proof of $\mathrm{Sat}(u, \varphi, v)$ with variables $u, v$, construct a $P$-proof of $\varphi$.

## Expansion

A polynomial-time algorithm producing tautologies hard for $P$ exists iff $P$ is not optimal (Krajíček-Pudlák), but this is close to a restatement, since reflection principles of a stronger system are hard for $P$. The proof reduces $\mathbf{Cert}$ to a more general task $\mathbf{Err}(L, \mathcal{F})$ of finding an input on which an $(\mathrm{NP} \cap \mathrm{coNP})/\mathrm{poly}$ algorithm errs on a language $L \in \mathrm{NE} \cap \mathrm{coNE}$ (with $\mathrm{TAUT}$ as the case used), and Theorem 4.1 shows, using the Nisan-Wigderson generator interpreted as a proof system and the hard one-way permutation (with a hard bit by the Goldreich-Levin theorem, giving a function of hardness $2^{\ell^{\Omega(1)}}$ against circuits), that no deterministic polynomial-time algorithm solves $\mathbf{Err}$ on all inputs for large lengths; in the $\mathbf{Cert}$ setting the input length is exponential in $k$, giving the $2^{O(k)}$ bound.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [One-way permutation families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-permutation.md)

## Proof depends on

- [Proof complexity generators and their tau-formulas](proof-complexity-generators.md)

## Sources

- J. Krajíček, "On the computational complexity of finding hard tautologies", *Bulletin of the London Mathematical Society* 46, 2014, doi:10.1112/blms/bdt071, arXiv:1212.1789v2 (Section 1 with the tasks Cert and Find, Section 2 with the circuit-based definition of exponentially hard one-way permutations, Theorem 4.1 and the corollary following it in Section 4, the definition of decent proof systems in Section 5, and the closing theorem of Section 6, whose statement writes Find$(P, c_0, c_1)$ although its proof treats the task Find$(P, c_0, d)$ with $|\alpha_k| \le k^{c_0}$ and proof-size exponent $d \ge c_0$, which is Find$(P, c_1, c_0)$ in the order of the definition).
