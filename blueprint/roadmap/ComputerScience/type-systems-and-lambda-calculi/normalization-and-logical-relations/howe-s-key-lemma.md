# Howe's key lemma

Consider the untyped lambda calculus with call-by-value evaluation $e \Downarrow_v v$ of closed terms to closed values (abstractions):
$v \Downarrow_v v$, and $e_1\, e_2 \Downarrow_v v$ if $e_1 \Downarrow_v \lambda x.\, e$, $e_2 \Downarrow_v v_2$ and $e[v_2/x] \Downarrow_v v$.

- Write $e \Downarrow_v$ if $e \Downarrow_v v$ for some $v$. A relation $S$ on closed terms is an *applicative simulation* if $e_1 \mathrel{S} e_2$ and $e_1 \Downarrow_v \lambda x.\, e_1'$ imply $e_2 \Downarrow_v \lambda x.\, e_2'$ with
  $e_1'[v/x] \mathrel{S} e_2'[v/x]$ for every closed value $v$. The largest one is *applicative similarity* $\lesssim_v$. It is extended to open terms by
  $\vec x \vdash e \lesssim_v e'$ if $e[\vec v/\vec x] \lesssim_v e'[\vec v/\vec x]$ for all closed values $\vec v$.
- For a relation $R$ on terms in context, its *Howe closure* $R^H$ is defined inductively: $\vec x \vdash x \mathrel{R^H} e$ if $\vec x \vdash x \mathrel{R} e$; $\vec x \vdash \lambda x.\, e_1 \mathrel{R^H} e_2$ if
  $\vec x, x \vdash e_1 \mathrel{R^H} e_1'$ and $\vec x \vdash \lambda x.\, e_1' \mathrel{R} e_2$; and $\vec x \vdash e_1\, e_2 \mathrel{R^H} e_3$ if $\vec x \vdash e_1 \mathrel{R^H} e_1'$, $\vec x \vdash e_2 \mathrel{R^H} e_2'$ and
  $\vec x \vdash e_1'\, e_2' \mathrel{R} e_3$.

**Lemma.** If $e_1 \Downarrow_v \lambda x.\, e$ and $\emptyset \vdash e_1 \mathrel{(\lesssim_v)^H} e_2$, then $e_2 \Downarrow_v \lambda x.\, e'$ for some $e'$ with
$\{x\} \vdash e \mathrel{(\lesssim_v)^H} e'$. The proof is by induction on the derivation of $e_1 \Downarrow_v \lambda x.\, e$, using that $(\lesssim_v)^H$ is compatible, contains
$\lesssim_v$, is closed under composition with $\lesssim_v$ on the right, and is substitutive for values.

Since $(\lesssim_v)^H$ is closed under value substitution, the lemma makes its restriction to closed terms an applicative simulation, so it is
contained in $\lesssim_v$; as $\lesssim_v \subseteq (\lesssim_v)^H$, the two coincide.

## Sources

- A. M. Pitts, "Howe's method for higher-order languages", in D. Sangiorgi and J. Rutten (eds.), *Advanced Topics in Bisimulation and Coinduction*, Cambridge University Press, 2011, Chapter 5, <https://www.cl.cam.ac.uk/~amp12/papers/howmho/howmho.pdf>: Section 5.2 (call-by-value evaluation), Definitions 5.3.1 and 5.4.1, Section 5.5 (rules How1–How3, Lemmas 5.5.1 and 5.5.3, Lemma 5.5.4 and the proof of Theorem 5.5.5). Section 5.9 gives the call-by-name analogue (key lemma 5.78).
