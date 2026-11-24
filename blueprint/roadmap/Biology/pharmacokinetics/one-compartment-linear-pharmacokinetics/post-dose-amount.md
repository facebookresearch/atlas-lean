# Post Dose Amount

The amount just after dose `n` in the fixed-spacing trajectory:
the sum of the first `n + 1` doses, each decayed from its event
time to `n * tau`. This is the event-time value of the trajectory
in `periodic_amount_decay`.
