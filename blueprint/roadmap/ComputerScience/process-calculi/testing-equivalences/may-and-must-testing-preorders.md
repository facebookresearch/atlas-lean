# May and must testing preorders

Consider CCS terms built from process variables $x, y, \dots$, $\mathrm{NIL}$, an undefined process $\Omega$, prefixes $\mu.p$ with $\mu$ in $\Delta \cup \bar\Delta \cup \{\tau\}$ (names, conames and the silent action), choice $p + q$, parallel composition $p \mid q$, relabelling $p[S]$ by a partial function $S$ on actions with $S(\tau) = \tau$ that is injective where it is defined, is defined at $\bar\lambda$ whenever it is defined at a visible action $\lambda$, and satisfies $S(\bar\lambda) = \overline{S(\lambda)}$, and recursion $\mathrm{rec}\, x . t$, which binds $x$; processes are the closed terms, those in which every variable is bound. The transition rules are the usual ones: in $p \mid q$ complementary actions $\lambda$ and $\bar\lambda$ synchronize into $\tau$. A closed term *converges*, $p \downarrow$, unless it contains an unguarded recursion or an unguarded occurrence of $\Omega$. An *observer* is a term over the same operators and a further action $\omega$ that reports success.

A *computation* from $o \mid p$ is a maximal sequence of $\tau$-transitions $o \mid p = o_0 \mid p_0 \xrightarrow{\tau} o_1 \mid p_1 \xrightarrow{\tau} \cdots$, finite only if its last term has no $\tau$-transition.

- $p$ *may satisfy* $o$ if $o \mid p \xrightarrow{\tau}{}^* q$ for some $q$ that can perform $\omega$.
- $p$ *must satisfy* $o$ if every computation from $o \mid p$ reaches some $o_n$ that can perform $\omega$, and whenever $o_k \mid p_k$ does not converge, some $o_{k'}$ with $k' \le k$ can perform $\omega$.

For closed processes, $p \sqsubseteq_{\mathrm{may}} q$ if every observer that $p$ may satisfy is one that $q$ may satisfy, $p \sqsubseteq_{\mathrm{must}} q$ if every observer that $p$ must satisfy is one that $q$ must satisfy, and $p \sqsubseteq_{\mathrm{test}} q$ if both hold. Each preorder induces an equivalence, $\simeq = \sqsubseteq \cap \sqsupseteq$; $\simeq_{\mathrm{test}}$ is testing equivalence.

## Sources

- R. De Nicola and M. C. B. Hennessy, "Testing equivalences for processes", *Theoretical Computer Science* 34(1–2):83–133, 1984, <https://www.scss.tcd.ie/Matthew.Hennessy/pubs/old/TCS84.pdf>: Section 1.2 (result sets, Definitions 1.2.1 and 1.2.3, Proposition 1.2.4, where $\sqsubseteq_{\mathrm{may}}$, $\sqsubseteq_{\mathrm{must}}$ and $\sqsubseteq_{\mathrm{test}}$ are written $\sqsubseteq_3$, $\sqsubseteq_2$ and $\sqsubseteq_1$), Section 2.1 (the operators, the conditions on the relabelling functions in $PER$ on p. 89, Definitions 2.1.1 and 2.1.2) and Section 2.2 (observers, computations, and the conditions (a) and (b) for may and must satisfaction).
