# Decode, then check

Accept an encoded trace exactly when it decodes and `checkThermalTrace`
accepts the decoded list. On a concrete encoding this is a closed Boolean computation, checked by
kernel reduction (`decide +kernel`).
