# Rest Factor pos iff

For `vr² ≤ 4`, `restFactor vr δ > 0` exactly on the window
`pulseRootLow vr < δ < pulseRootHigh vr`. For `δ > 0` this is the rising-pulse condition of
`isRisingAfterPulse_iff`. Every `δ` in the window is positive when `vr ≤ -1`
(`pulseRootLow_nonneg`); for `-1 < vr < 2` the window is nonempty and also contains nonpositive
`δ` (`pulseRootLow_lt_pulseRootHigh`, `pulseRootLow_neg`); at `vr = ±2` it is empty.
