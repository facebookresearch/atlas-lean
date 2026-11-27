# Hybrid argument, uniform form

For a sequence of games $H_0, H_1, \dots$, if $\mathrm{Adv}(H_i, H_{i+1}) \le \varepsilon$ for every
$i < n$, then $\mathrm{Adv}(H_0, H_n) \le n \varepsilon$, where $\mathrm{Adv}$ is the distinguishing
advantage. The same bound for a sequence of distributions $p_0, \dots, p_k$ on a finite type and an event $E$ reads $|p_0(E) - p_k(E)| \le k \varepsilon$ when consecutive distributions give $E$ probabilities within $\varepsilon$ (take the Boolean game at step $i$ to be the indicator of $E$ under $p_i$).
