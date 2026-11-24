# Area under the queue length over one cycle is λ R² μ / (2 (μ − λ))

Let the arrival rate `λ` and the service rate `μ` satisfy `0 < λ < μ`, and let the red duration
`R ≥ 0` and the green duration `G ≥ 0` satisfy the capacity condition `λ (R + G) ≤ μ G`, under which
the queue clears by the end of the cycle. Then the [queue length](queue-len.md) `Q(t)` satisfies

`∫_0^{R + G} Q(t) dt = λ R² μ / (2 (μ - λ))`,

the area of the triangle traced by the queue during one cycle of length `R + G`.
