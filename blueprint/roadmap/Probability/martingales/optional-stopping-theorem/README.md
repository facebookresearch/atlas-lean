# Optional stopping theorem

Let $\mu$ be a measure on $\Omega$ and $(\mathcal{G}_n)_{n \ge 0}$ a filtration such that the restriction of $\mu$ to each $\mathcal{G}_n$ is σ-finite (for example, $\mu$ a probability measure), and let $(f_n)_{n \ge 0}$ be a real-valued martingale with respect to $(\mathcal{G}_n)$ and $\mu$. Let $\tau$ and $\pi$ be stopping times with values in $\mathbb{N} \cup \{\infty\}$, and let $N$ be a natural number with $\tau(\omega) \le \pi(\omega) \le N$ for every $\omega$. Then $\int f_\tau \, d\mu = \int f_\pi \, d\mu$, where $f_\tau(\omega) = f_{\tau(\omega)}(\omega)$.

## Idea

A martingale models a fair game, and optional stopping says that no rule for when to quit, using only past information and a bounded time, changes the expected outcome. For bounded times the proof is a finite sum:

$$f_\pi - f_\tau = \sum_{k < N} \mathbf{1}_{\{\tau \le k < \pi\}} (f_{k+1} - f_k),$$

and each indicator is $\mathcal{G}_k$-measurable, so each term has integral zero. Boundedness matters: a simple random walk started at $0$ and stopped when it first reaches $1$ has stopped value $1$ although it starts at $0$, and the stopping time is finite almost surely. For unbounded times, uniform integrability replaces boundedness. The card also holds the supermartingale inequalities, the submartingale form at an almost surely bounded time with the lemma that a stopped submartingale is again a submartingale, the conditional forms, the forms for uniformly integrable martingales and submartingales at unbounded times, and a continuous-time version.

## Statements

- [Optional stopping for martingales at two bounded stopping times](expected-stopped-value-eq.md)
- [Optional stopping for martingales at a bounded stopping time](expected-stopped-value-eq-zero.md): one stopping time
- [Optional stopping for supermartingales at two bounded stopping times](expected-stopped-value-anti-mono.md): supermartingale form
- [Optional stopping for supermartingales at a bounded stopping time](expected-stopped-value-le.md): supermartingale form, one stopping time
- [Optional stopping for submartingales at a bounded stopping time](bounded-optional-stopping.md): the submartingale form at an almost surely bounded time
- [Stopped submartingales are submartingales](stopped-process.md): lemma used for optional stopping at bounded times
- [Bounded optional stopping, conditional form](stopped-value-le-cond-exp-stopped-value.md): conditional form
- [Bounded optional stopping, conditional form, supermartingale dual](cond-exp-stopped-value-le-stopped-value.md): conditional form, supermartingale dual
- [Value of a process at a possibly infinite time](stopped-value-at-top.md): definition used by the unbounded forms
- [Stopped filtration](stopped-filtration.md): definition used by the unbounded forms
- [Levels of the stopped filtration](stopped-filtration-apply.md): basic property of the stopped filtration
- [The event that the stopping time is infinite is measurable for the stopped filtration](measurable-set-eq-top-i-sup-stopped-filt.md): lemma used for the unbounded forms
- [Infinite-time parts of limit-σ-algebra sets are measurable for the stopped filtration](measurable-set-inter-eq-top-i-sup-stoppe.md): lemma used for the unbounded forms
- [The stopped filtration generates the stopping-time σ-algebra](i-sup-stopped-filtration.md): lemma used for the unbounded forms
- [Stopping at a later time does not change the stopped value](stopped-value-at-top-stopped-process-of.md): lemma used for the unbounded forms
- [Optional stopping preserves uniform integrability of martingales](uniform-integrable-stopped-process-of-un-2.md): uniform integrability of the stopped martingale
- [General optional stopping, uniform integrability preservation](uniform-integrable-stopped-process-of-un.md): uniform integrability, submartingale case
- [Stopped value as conditional expectation of the limit](stopped-value-at-top-ae-eq-cond-exp-limi.md): unbounded times: stopped value as conditional expectation of the limit
- [Conditional optional stopping with UI of the stopped process](stopped-value-at-top-ae-eq-cond-exp-stop.md): unbounded times, conditional form
- [Conditional optional stopping for uniformly integrable submartingales](stopped-value-at-top-le-cond-exp-stopped.md): unbounded times, submartingale conditional form
- [General optional stopping for uniformly integrable martingales](integral-stopped-value-at-top-eq-of-unif.md): unbounded times, uniformly integrable martingales
- [Expectation form of optional stopping for uniformly integrable submartingales](integral-stopped-value-at-top-mono-of-un.md): unbounded times, submartingale expectation form
- [General optional stopping, expectation inequality](integral-stopped-value-at-top-of-uniform.md): unbounded times, expectation inequality
- [Optional stopping theorem in continuous time](stopped-value-ae-eq-cond-exp-of-le-of-co.md): continuous-time form

## Related topics

- [Optimal stopping and the Snell envelope](../optimal-stopping-and-the-snell-envelope/snell-stopping-time-optimal.md): choosing the stopping time to maximise the expected gain; the optimality proof applies bounded optional stopping to the Snell envelope.
