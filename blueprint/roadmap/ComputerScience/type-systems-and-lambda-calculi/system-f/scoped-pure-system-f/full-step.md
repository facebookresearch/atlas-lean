# One-step full reduction of System F terms

One-step full reduction on [scoped System F terms](tm.md) $\mathrm{Tm}_{n,m}$ is the least relation $t \rightsquigarrow t'$ containing term beta reduction $(\lambda A.\, b)\, a \rightsquigarrow b[a]$, which [instantiates the newest term binder](instantiate-2.md) of $b$ with $a$, and type beta reduction $(\Lambda b)\, [A] \rightsquigarrow b[A]$, and closed under every term and type context: under term abstraction $\lambda A.\, -$, on either side of an application, under type abstraction $\Lambda -$ and in the function position of a type application.

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 11 (System F and its reduction rules), <https://www.paultaylor.eu/stable/prot.pdf>
