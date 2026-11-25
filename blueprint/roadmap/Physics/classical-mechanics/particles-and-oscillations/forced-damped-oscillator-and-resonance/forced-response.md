# Forced response of the mass–spring–damper with given initial data

Let `m > 0`, `c ≥ 0` and `k > 0`, and let `F`, `Ω`, `x₀` and `v₀` be real numbers. The forced
response at time `t` is

`x(t) = x_p(t) + y(t)`,

where `x_p` is the [particular response](particular-response.md) and `y(t)` is the coordinate at
time `t` of the selected free trajectory of the [damped oscillator](mass-spring-damper.md) with
[initial conditions](initial-conditions.md) `(x₀ - x_p(0), v₀ - v_p(0))`, `v_p` being the
[particular velocity](particular-velocity.md): both initial values are corrected by the particular
response. When the [steady-state denominator](steady-state-denominator.md) `D` is nonzero it solves
the forced equation with initial position `x₀` and velocity `v₀`
([properties](forced-response-spec.md)). With the convention `u / 0 = 0`, at `D = 0` (the undamped
exact resonance `c = 0`, `k = m Ω²`) `x_p ≡ 0` and `v_p ≡ 0`, so the forced response is the free
trajectory from `(x₀, v₀)`, which does not solve the forced equation when `F ≠ 0`.
