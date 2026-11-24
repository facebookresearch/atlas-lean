# Adaptive Minrun Scan Invariant

State carried between scan iterations. `emittedLeScanned` records that
every already-emitted minrun target was covered by the actual runs consumed so
far; natural runs may make the inequality strict.
