# Without superthreshold drive the threshold is never reached

Let `u_r < u_∞ ≤ θ` and `τ > 0`. Then `u_∞ - (u_∞ - u_r) e^(-t/τ) < θ` for every `t ≥ 0`: the
voltage relaxing from the reset value `u_r` toward the steady value `u_∞` never reaches the
threshold `θ`. At `u_∞ = θ` it approaches the threshold only asymptotically
([asymptotic approach](lif-tendsto.md)).
