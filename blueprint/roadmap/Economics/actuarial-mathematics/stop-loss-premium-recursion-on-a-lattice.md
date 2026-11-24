# Stop-loss premiums on an arithmetic lattice

Let $h > 0$ and let $S \ge 0$ be an integrable random variable with $S/h \in \{0, 1, 2, \dots\}$ almost surely. Then for every integer $j \ge 0$, $E[(S - (j+1)h)^+] = E[(S - jh)^+] - h\,P(S > jh)$, because on the lattice $(S - jh)^+ - (S - (j+1)h)^+ = h\mathbf 1\{S > jh\}$. The strict inequality $S > jh$ matters, and the recursion is not valid for severities with continuous distributions.
